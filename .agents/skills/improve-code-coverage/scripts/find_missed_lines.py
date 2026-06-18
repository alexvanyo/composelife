import xml.etree.ElementTree as ET
import os
import sys

if len(sys.argv) < 2:
    print("Usage: python3 find_missed_lines.py <FileName.kt>")
    sys.exit(1)

filename = sys.argv[1]

script_dir = os.path.dirname(os.path.abspath(__file__))
repo_root = os.path.abspath(os.path.join(script_dir, "..", "..", "..", ".."))
xml_path = os.path.join(repo_root, 'build/reports/jacoco/jacocoDebugUnitTestCoverageReport/jacocoDebugUnitTestCoverageReport.xml')

if not os.path.exists(xml_path):
    print(f"Error: Jacoco report XML not found at {xml_path}")
    print("Please run: ./gradlew jacocoDebugUnitTestCoverageReport")
    sys.exit(1)

tree = ET.parse(xml_path)
root = tree.getroot()

found = False
for package in root.findall('.//package'):
    for sourcefile in package.findall('.//sourcefile'):
        if sourcefile.get('name') == filename:
            print(f"File: {filename}")
            found = True
            for line in sourcefile.findall('line'):
                nr = line.get('nr')
                mi = int(line.get('mi'))
                ci = int(line.get('ci'))
                mb = int(line.get('mb'))
                cb = int(line.get('cb'))
                if mi > 0 or mb > 0:
                    print(f"Line {nr}: Missed Inst={mi}, Covered Inst={ci}, Missed Branch={mb}, Covered Branch={cb}")

if not found:
    print(f"File {filename} not found in the Jacoco coverage report.")
