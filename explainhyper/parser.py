import argparse

def parse_arguments():
    parser = argparse.ArgumentParser(description='Clean up counterexample and add output values. Generates a new augmented counterexample file.')
    parser.add_argument('-cex', required=True, help='the counterexample file to be processed')
    parser.add_argument('-aag', required=True, help='the aiger file containing the system circuit') 
    parser.add_argument('-f', required=True, help='the formula that was model checked')
    parser.add_argument('-outName', required=True, help='name of output file (without file ending)')
    parser.add_argument('-stateMachine', required=False, help='The state machine that is debugged(with file ending)')
    args = parser.parse_args()
    return args