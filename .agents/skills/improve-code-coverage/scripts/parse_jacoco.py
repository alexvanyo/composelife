import xml.etree.ElementTree as ET
import os
import sys

# Get repository root (assumed to be parent of the script's directory if the script is in .agents/skills/improve-code-coverage/scripts/)
script_dir = os.path.dirname(os.path.abspath(__file__))
repo_root = os.path.abspath(os.path.join(script_dir, "..", "..", "..", ".."))

xml_path = os.path.join(repo_root, 'build/reports/jacoco/jacocoDebugUnitTestCoverageReport/jacocoDebugUnitTestCoverageReport.xml')

if not os.path.exists(xml_path):
    print(f"Error: Jacoco report XML not found at {xml_path}")
    print("Please run: ./gradlew jacocoDebugUnitTestCoverageReport")
    sys.exit(1)

tree = ET.parse(xml_path)
root = tree.getroot()

classes = []
for package in root.findall('.//package'):
    package_name = package.get('name')
    for cls in package.findall('.//class'):
        class_name = cls.get('name')
        
        # Get counters
        inst_missed = 0
        inst_covered = 0
        branch_missed = 0
        branch_covered = 0
        
        for counter in cls.findall('counter'):
            type_ = counter.get('type')
            missed = int(counter.get('missed'))
            covered = int(counter.get('covered'))
            if type_ == 'INSTRUCTION':
                inst_missed = missed
                inst_covered = covered
            elif type_ == 'BRANCH':
                branch_missed = missed
                branch_covered = covered
                
        total_inst = inst_missed + inst_covered
        if total_inst > 0:
            coverage = inst_covered / total_inst
            classes.append({
                'package': package_name,
                'class': class_name,
                'inst_missed': inst_missed,
                'inst_covered': inst_covered,
                'branch_missed': branch_missed,
                'branch_covered': branch_covered,
                'coverage': coverage
            })

# Sort classes by missed instructions (highest first)
classes.sort(key=lambda x: x['inst_missed'], reverse=True)

# Write report to a text file in the workspace build directory
output_path = os.path.join(repo_root, 'build/jacoco_report.txt')
with open(output_path, 'w') as f:
    f.write("Package\tClass\tMissed Inst\tCovered Inst\tMissed Branch\tCovered Branch\tCoverage %\n")
    for c in classes:
        f.write(f"{c['package']}\t{c['class']}\t{c['inst_missed']}\t{c['inst_covered']}\t{c['branch_missed']}\t{c['branch_covered']}\t{c['coverage']:.2%}\n")
print(f"Report written to {output_path}. Total classes: {len(classes)}")
