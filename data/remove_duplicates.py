
import sys

def remove_duplicates(input_file, output_file=None):
    seen = set()
    lines_to_write = []
    
    with open(input_file, 'r') as f:
        for line in f:
            if line not in seen:
                seen.add(line)
                lines_to_write.append(line)
    
    if output_file:
        with open(output_file, 'w') as f:
            f.writelines(lines_to_write)
    else:
        # Print to stdout
        for line in lines_to_write:
            print(line, end='')

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python remove_duplicates.py <input_file> [output_file]")
        print("If output_file is not specified, results are printed to stdout")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None
    
    remove_duplicates(input_file, output_file)
    
    if output_file:
        print(f"Duplicates removed. Output written to {output_file}")
