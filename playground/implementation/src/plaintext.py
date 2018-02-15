import serial

meh = raw_input("Press Enter to start sending messages (you might want to start the other script first)...")

messages = [bytearray("This i01"), bytearray("s a lon02"), bytearray("g numb03"), bytearray("ered, 04"), bytearray("secret05"), bytearray(" text:06"), bytearray(" For y07"), bytearray("our ey07"), bytearray("esonly08")]

ser = serial.Serial()

ser = serial.Serial(
port = "/dev/ttyACM0",
baudrate = 57600,
bytesize = serial.EIGHTBITS, 
parity = serial.PARITY_NONE,
stopbits = serial.STOPBITS_ONE, 
timeout = 1,
xonxoff = False,
rtscts = True,
dsrdtr = True,
writeTimeout = 2
)

ser.open

seqNo = -1
for x in messages:
    seqNo = seqNo + 1
    seqP1 = (seqNo & 0x7F) | 0x80
    ser.write(chr(seqP1))
    seqP2 = ((seqNo >> 7) & 0x7F) | 0x80
    ser.write(chr(seqP2))
    for c in x:
        ser.write((c & 0x7F))


ser.write(b'text')

ser.close
