#include "driver.c"

//Protocol definitions, how many data blocks and sequence number blocks we have
//Each block is 1 byte and the MSB is header information
#define NUM_DATA_BLOCKS         8
#define NUM_SEQNO_BLOCKS        2
#define MSG_SIZE                (NUM_DATA_BLOCKS+NUM_SEQNO_BLOCKS)

//Definitions for the crypto key, the number of blocks as well as the block size
#define NUM_KEY_BLOCKS          10
#define KEY_BLOCK_SIZE          NUM_DATA_BLOCKS
#define KEY_SIZE                (NUM_KEY_BLOCKS * KEY_BLOCK_SIZE)


void shift_buffer(char *buffer)
{
    for(int k = MSG_SIZE - 1; k > 0; k--) {
       buffer[k] = buffer[k-1];
    }
}

_Bool validate_headers(char *buffer) {
   _Bool valid = 1;
   for(int i = 0; i < NUM_DATA_BLOCKS; i++){
      char msb = (buffer[i] & 0xFF) >> 7;
      valid &= (msb == 0);
   }
   for(int i = NUM_DATA_BLOCKS; i < NUM_KEY_BLOCKS; i++){
      char msb = (buffer[i] & 0xFF) >> 7;
      valid &= (msb == 1);
   }
   return valid;
}

int get_seq_no(char *buffer){
   int seq_no = 0;
   for(int i = 0; i < NUM_SEQNO_BLOCKS; i++){
       seq_no += (buffer[MSG_SIZE - 1 - i] & 0x7f) << (i * 7); 
   }
   return seq_no;
}

void test_fill_key(char *key){
  for(int i = 0; i < KEY_SIZE; i++){
    key[i] = 0x0;
  }
}

void encrypt(int seq_no, char *buffer, char *key){
  for(int i = 0; i < NUM_DATA_BLOCKS; i++){
    buffer[i] = buffer[i] ^ key[seq_no * KEY_BLOCK_SIZE + i];
  }
}

void clean_data_headers(char *buffer){
  for(int i = 0; i < NUM_DATA_BLOCKS; i++){
    buffer[i] = (buffer[i] & 0x7F);
  }
}

void write_to_uart(char *buffer){
  for(int i = 0; i < MSG_SIZE; i++){
    uart_send(buffer[i]);
  }
}



void main ( ) {
    uart_init();

    //Send Welcome
    uart_send_string ("\nBBC micro:bit echo\n");

    char buffer[MSG_SIZE];
    char key[KEY_SIZE];
    int last_seq_no = -1;

    test_fill_key(key);

    //Start echoing
    while (1) {
      unsigned int v = uart_read ();
      shift_buffer(buffer);
      buffer[0] = v;
      if(!validate_headers(buffer)){
          continue;
      }
      int seq_no = get_seq_no(buffer);
      if(seq_no <= last_seq_no){
          continue;
      }

      //TODO stop when key is exhausted

      last_seq_no = seq_no;
      //int key_index = seq_no * MSG_SIZE;
      
      encrypt(seq_no, buffer, key);

      clean_data_headers(buffer);

      write_to_uart(buffer);
    }
    
}
