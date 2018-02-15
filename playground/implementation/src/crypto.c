#include "uart.h"
#include "crypto.h"

/* Forward declarations of private functions */

void shift_buffer(char *buffer);
_Bool validate_headers(char *buffer);
int get_seq_no(char *buffer);
void test_fill_key(char *key);
void encrypt(int seq_no, char *buffer, char *key);
void clean_data_headers(char *buffer);
void write_to_uart(char *buffer);

/* Public Functions */
void process_messages(){
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

/*Private Functions*/

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
