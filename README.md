# AirAcousticsSuite

A Python GUI for automating the characterisation of air-coupled acoustic and ultrasonic transducers. It communicates directly with lab equipment (oscilloscopes, function generators, and Arduino-controlled rotary stages) to run sweeps, capture bursts, and plot directivity.

Hardware Requirements
To use the automated features, you need:

A VISA-compatible Oscilloscope (e.g., Keysight, Tektronix).

A VISA-compatible Function Generator.

(Optional) An Arduino connected via USB for polar plots. The software sends absolute position commands in the format G<angle>\n and jog commands like J1\n or J-1\n.
