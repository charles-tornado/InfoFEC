#include "windows.h"

#include <algorithm>  // for std::copy
#include <fstream>
#include <iostream>
#include <iterator>  // for std::istreambuf_iterator
#include <string>
#include <sstream>
#include <cstring>
#include <cstringt.h>
#include <time.h>
#include "invert_GF_matrix.h"
#ifdef _MSC_VER
#  pragma warning(push)
#  pragma warning(disable: 4100 4127 4189 4244)
#endif
#include "cryptopp/aes.h"
#include "cryptopp/config.h"
#include "cryptopp/files.h"
#include "cryptopp/filters.h"
#include "cryptopp/modes.h"
#ifdef _MSC_VER
#  pragma warning(pop)
#endif

using namespace std;

int table[256];
int arc_table[256];
int inverse_table[256];

namespace {
	const std::string original_file("1.rmvb");
	const std::string encrypted_file("2.rmvb");
	const std::string decrypted_file("3.rmvb");

	const int k = 3;
	const int n = 4;
	const int bytes = 16;

	int i, j, l, g;//循环系数	
	int groups;//总的组数
	long groups_seqence = 0;//groups号
	int groups_bytes = bytes*k;

	const int key_size(CryptoPP::AES::DEFAULT_KEYLENGTH);
	const int iv_size(CryptoPP::AES::BLOCKSIZE);


	unsigned char *a_ij = (unsigned char*)malloc(sizeof(unsigned char)*n*k);//系数矩阵
	unsigned char *xi = (unsigned char*)malloc(sizeof(unsigned char)*bytes);//每个数据包的元素（bytes个字节）
	unsigned char *recover_data = (unsigned char*)malloc(sizeof(unsigned char)*bytes*k);
	unsigned char *c = (unsigned char *)malloc(sizeof(unsigned char)* k*k);//逆矩阵
}

int mul(int x, int y)
{
	if (!x || !y)
		return 0;

	return table[(arc_table[x] + arc_table[y]) % 255];
}

void GetKeyAndIv(byte* key, byte* iv) {
	HW_PROFILE_INFOA profile;
	GetCurrentHwProfileA(&profile);
	char* guid(profile.szHwProfileGuid);
	assert(std::char_traits<char>::length(guid) >= key_size + iv_size);
	// Assign first 'key_size' chars of GUID to 'key'
	std::copy(guid, guid + key_size, key);
	// Assign next 'iv_size' chars of GUID to 'iv'
	std::copy(guid + key_size, guid + key_size + iv_size, iv);
};

unsigned char * padding(unsigned char * buffer, int length){

	groups = ceil((float)length / groups_bytes);
	int remainder_bytes = length % groups_bytes;
	if (remainder_bytes != 0)
	{
		unsigned char * str = new unsigned char[groups*groups_bytes];
		memcpy(str, buffer, length);
		memset(str + length, 0, groups_bytes - remainder_bytes);
		return str;
	}
	return buffer;

}
void initialize_FEC_coefficient_matrix(int k, int n){
	memset(a_ij, 0, sizeof(unsigned char)*n*k);
	for ( i = 0; i < k; i++)
	{
		a_ij[i*k+i] = 1;
	}
	unsigned char *b = (unsigned char*)malloc(sizeof(unsigned char)*(k+1)*k);//用于构造系数矩阵的模块
	memset(b, 1, sizeof(unsigned char)*(k+1)*k);
	for ( i = 0; i < k; i++)
	{
		b[k + i*k + i] = 0;
	}

	for ( i = k*k, j = 0; i < n*k; i++, j++)
	{
		a_ij[i] = b[j%((k+1)*k)];
	}
	free(b);
}

void FEC_encode(const char *origin_text,int length){
	std::ofstream outfile;
	outfile.open(encrypted_file.c_str(), ofstream::app | ofstream::out | ofstream::binary);//create output file

	unsigned char* str = padding((unsigned char*)origin_text, length);
	memset(xi, 0, sizeof(unsigned char)*bytes);

	for (g = 0; g < groups; g++){

		for (l = 0; l < n; l++)
		{
			for (j = 0; j < bytes; j++)
			{
				for (i = 0; i < k; i++)
				{
					xi[j] ^= mul(a_ij[i + l*k], str[g*groups_bytes + (i*bytes + j)]);// str 0-255
				}
			}
			outfile.write((const char *)xi, bytes);
			memset(xi, 0, sizeof(unsigned char)*bytes);

		}
	}

	outfile.close();
}

void FEC_decode(char *encode_text, int *length){
	int encode_length = *length;
	char * buffer = new char[encode_length];
	memcpy(buffer, encode_text, encode_length);

	groups = ceil((float)encode_length / (n*bytes));

	memset(xi, 0, sizeof(unsigned char)*bytes);

	for (g = 0; g < groups; g++){

		int *receive_id = (int*)malloc(sizeof(int)*k);
		memset(receive_id, 0, sizeof(int)*k);
		memset(recover_data, 0, sizeof(unsigned char)*bytes*k);
		int count = 0;
		do
		{
			for (i = 0; i < k; i++)
			{
				//初始假设收到的为n个包中的前k个包
				receive_id[i] = (i + count) % n + 1;

			}
			for (i = 0; i<k; i++)
			{
				for (j = 0; j<k; j++)
				{
					c[i*k + j] = a_ij[(receive_id[i] - 1)*k + j];
				}

			}
			count++;

		} while (!inv(c, k));


		for (l = 0; l<k; l++)
		{
			for (j = 0; j<bytes; j++)
			{
				for (i = 0; i<k; i++)
				{
					recover_data[l*bytes + j] ^= mul(c[l*k + i], buffer[g*n*bytes + (receive_id[i] - 1)*bytes + j]);

				}
				recover_data[l*bytes + j] = recover_data[l*bytes + j];
			}

		}
		memcpy(encode_text + g*groups_bytes, recover_data, groups_bytes);
	}
	*length = groups * groups_bytes;
	delete buffer;
}


void Encrypt() {
	// Initialise the key and IV
	byte key[key_size] = { 0 }, iv[iv_size] = { 0 };
	GetKeyAndIv(key, iv);

	std::ifstream t;
	int length;
	t.open(original_file.c_str(), std::ios::binary);      // open input file  
	t.seekg(0, std::ios::end);    // go to the end  
	length = t.tellg();           // report location (this is the length)  
	t.seekg(0, std::ios::beg);    // go back to the beginning  
	char * buffer = new char[length];    // allocate memory for a buffer of appropriate dimension  
	t.read(buffer, length);       // read the whole file into the buffer  
	t.close();                    // close file handle  



	// Encrypt
	CryptoPP::AES::Encryption cipher(key, key_size);
	CryptoPP::CBC_Mode_ExternalCipher::Encryption encryption(cipher, iv);
	std::string cipher_text;
	CryptoPP::StreamTransformationFilter filter(encryption,
		new CryptoPP::StringSink(cipher_text));
	filter.Put(reinterpret_cast<const byte*>(buffer), length);
	filter.MessageEnd();

	//FEC_encode
	FEC_encode(cipher_text.c_str(), cipher_text.size());

}

void Decrypt() {
	// Initialise the key and IV
	byte key[key_size] = { 0 }, iv[iv_size] = { 0 };
	GetKeyAndIv(key, iv);

	std::ifstream t;
	int *length = new int;
	*length = 0;
	t.open(encrypted_file.c_str(), std::ios::binary);      // open input file  
	t.seekg(0, std::ios::end);    // go to the end  
	*length = t.tellg();           // report location (this is the length)  
	t.seekg(0, std::ios::beg);    // go back to the beginning  
	char * buffer = new char[*length];    // allocate memory for a buffer of appropriate dimension  
	t.read(buffer, *length);       // read the whole file into the buffer  
	t.close();                    // close file handle  


	//FEC_decode
	FEC_decode(buffer, length);

	// Decrypt
	CryptoPP::AES::Decryption cipher(key, key_size);
	CryptoPP::CBC_Mode_ExternalCipher::Decryption decryption(cipher, iv);
	std::string decrypted_test;
	CryptoPP::StreamTransformationFilter filter(decryption,
		new CryptoPP::StringSink(decrypted_test));
	filter.Put(reinterpret_cast<const byte*>(buffer),*length);
	filter.MessageEnd();

	// Dump decrypted text
	std::ofstream outfile(decrypted_file.c_str(), std::ios::binary);
	outfile.write(decrypted_test.c_str(), decrypted_test.size());
	outfile.close();
}

void table_initialize(){
	table[0] = 1;//g^0
	for (i = 1; i < 255; ++i)//生成元为x + 1
	{
		//下面是m_table[i] = m_table[i-1] * (x + 1)的简写形式
		table[i] = (table[i - 1] << 1) ^ table[i - 1];

		//最高指数已经到了8，需要模上m(x)
		if (table[i] & 0x100)
		{
			table[i] ^= 0x11B;//用到了前面说到的乘法技巧
		}
	}



	for (i = 0; i < 255; ++i)
		arc_table[table[i]] = i;



	for (i = 1; i < 256; ++i)//0没有逆元，所以从1开始
	{
		int k = arc_table[i];
		k = 255 - k;
		k %= 255;//m_table的取值范围为 [0, 254]
		inverse_table[i] = table[k];
	}

}


int main() {
	table_initialize();
	initialize_FEC_coefficient_matrix(k, n);
	clock_t start, end;
	double totaltime;
	try {
		start = clock();

//		Encrypt();
		Decrypt();


		end = clock();
		totaltime = (double)(end - start) / CLOCKS_PER_SEC;
		cout << "此程序运行时间为" << totaltime << "秒！" << endl;


		cin.get();
	}
	catch (const CryptoPP::Exception& exception) {
		std::cout << "Caught exception: " << exception.what() << '\n';
		return -1;
	}
	return 0;
}