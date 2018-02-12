import serial

ser = serial.Serial()
ser.baudrate = 57600
ser.port = '/dev/ttyUSB0'
ser.open
for x in range(0, 20):
	s = ser.read(10)
	print(s)

ser.close