#include "uart.h"
#include "crypto.h"

/* Forward declarations of private functions */
void shift_buffer(char *buffer);
int validate_seq_headers(char *buffer);
int validate_data_headers(char *buffer);
int is_seq_in_order(int seq_no, int last_seq_no);
unsigned int get_seq_no(char *buffer);
int valid_msg(char *buffer, int seq_no, int last_seq_no);
void encrypt(unsigned int seq_no, char *buffer, char *key);
void zero_data_headers(char *buffer);
void write_to_uart(char *buffer);

int test(int meh);
const unsigned int MAX_SEQ_NO = 16383;

/* Public Functions */
void process_messages(char *key){
    
    char buffer[10];
    unsigned int last_seq_no = 0;

    //Start echoing
    while (last_seq_no < MAX_SEQ_NO) {
      //Read a byte from uart
      unsigned int v = uart_read ();

      //Shift the buffer
      shift_buffer(buffer);

      //Add the latest data to the start of the buffer
      buffer[9] = v;

      unsigned int curr_seq_no = get_seq_no(buffer);

      //If headers or sequence number is invalid, continue
      if(valid_msg(buffer, curr_seq_no, last_seq_no)){
          last_seq_no = curr_seq_no;
      
          encrypt(last_seq_no, buffer, key);

          zero_data_headers(buffer);

          write_to_uart(buffer);
      }
    }
}


/*Private Functions*/

int __attribute__ ((noinline)) is_seq_in_order(int seq_no, int last_seq_no){
  return (last_seq_no < seq_no) && (seq_no < MAX_SEQ_NO);
}

int valid_msg(char *buffer, int seq_no, int last_seq_no){
    //Check whether the headers are valid
    int is_valid = validate_seq_headers(buffer);
    is_valid &= validate_data_headers(buffer);

    //Check whether the sequence number is  
    is_valid &= is_seq_in_order(seq_no, last_seq_no);
    return is_valid;
}

void shift_buffer(char *buffer)
{
  buffer[0] = buffer[1];
  buffer[1] = buffer[2];
  buffer[2] = buffer[3];
  buffer[3] = buffer[4];
  buffer[4] = buffer[5];
  buffer[5] = buffer[6];
  buffer[6] = buffer[7];
  buffer[7] = buffer[8];
  buffer[8] = buffer[9];
  buffer[9] = 0;
}

int validate_seq_headers(char *buffer) {
  int valid = 1;
  for(int i = 0; i < NUM_SEQNO_BLOCKS; i++){
    char msb = (buffer[i] & 0XFF) >> 7;
    valid &= (msb == 1);
  }
  return valid;
}

int validate_data_headers(char *buffer) {
   int valid = ~((buffer[2] |
                  buffer[3] |
                  buffer[4] |
                  buffer[5] |
                  buffer[6] |
                  buffer[7] |
                  buffer[8] |
                  buffer[9]) >> 7);

   return valid;
}

unsigned int get_seq_no(char *buffer){
   unsigned int seq_no = (buffer[0] & 0x7f) << 7;
   seq_no += (buffer[1] & 0x7f);
   return seq_no;
}

void encrypt(unsigned int seq_no, char *buffer, char *key){
  int base_index = 8*(seq_no -1); //last_seq_no starts at 0, we want to use the first 8 bytes of the key
  buffer[2] = buffer[2] ^ key[base_index];
  buffer[3] = buffer[3] ^ key[base_index + 1];
  buffer[4] = buffer[4] ^ key[base_index + 2];
  buffer[5] = buffer[5] ^ key[base_index + 3];
  buffer[6] = buffer[6] ^ key[base_index + 4];
  buffer[7] = buffer[7] ^ key[base_index + 5];
  buffer[8] = buffer[8] ^ key[base_index + 6];
  buffer[9] = buffer[9] ^ key[base_index + 7];
}

void zero_data_headers(char *buffer){
  buffer[2] = (buffer[2] & 0x7F);
  buffer[3] = (buffer[3] & 0x7F);
  buffer[4] = (buffer[4] & 0x7F);
  buffer[5] = (buffer[5] & 0x7F);
  buffer[6] = (buffer[6] & 0x7F);
  buffer[7] = (buffer[7] & 0x7F);
  buffer[8] = (buffer[8] & 0x7F);
  buffer[9] = (buffer[9] & 0x7F);
}

void write_to_uart(char *buffer){
  uart_send(buffer[0]);
  uart_send(buffer[1]);
  uart_send(buffer[2]);
  uart_send(buffer[3]);
  uart_send(buffer[4]);
  uart_send(buffer[5]);
  uart_send(buffer[6]);
  uart_send(buffer[7]);
  uart_send(buffer[8]);
  uart_send(buffer[9]);
}
