#!/usr/bin/env python3
import sys
import json
import re

def main():
    try:
        data = json.load(sys.stdin)
    except Exception as e:
        print(f"Error parsing JSON input: {e}", file=sys.stderr)
        sys.exit(1)

    print("=== CI CHECK ROLLUP ===")
    status_rollup = data.get("statusCheckRollup", [])
    if not status_rollup:
        print("No status check rollup data found.")
    else:
        for check in status_rollup:
            name = check.get("name", "Unknown")
            status = check.get("status", "Unknown")
            conclusion = check.get("conclusion")
            url = check.get("detailsUrl", "")
            
            # Extract run ID from detailsUrl
            # Example: https://github.com/alexvanyo/composelife/actions/runs/29071783380/job/...
            run_id_match = re.search(r"/runs/(\d+)", url)
            run_id = run_id_match.group(1) if run_id_match else "N/A"

            if status != "COMPLETED":
                print(f"[{status}] {name} (Run ID: {run_id}) - {url}")
            elif conclusion != "SUCCESS":
                print(f"[FAILED] {name} (Run ID: {run_id}) - {conclusion} - {url}")
            else:
                print(f"[PASSED] {name}")

    print("\n=== REVIEW COMMENTS ===")
    reviews = data.get("reviews", [])
    has_comments = False
    for review in reviews:
        author = review.get("author", {}).get("login", "Unknown")
        state = review.get("state", "COMMENTED")
        submitted_at = review.get("submittedAt", "")
        body = review.get("body", "").strip()
        
        comments = review.get("comments", [])
        if comments or body:
            has_comments = True
            print(f"Review by @{author} [{state}] ({submitted_at}):")
            if body:
                print(f"  Overall Body: {body}")
            for comment in comments:
                c_id = comment.get("id")
                c_path = comment.get("path")
                c_line = comment.get("line")
                c_body = comment.get("body", "").strip()
                print(f"  - File: {c_path}:{c_line} (ID: {c_id})")
                print(f"    Comment: {c_body}")
                print()

    if not has_comments:
        print("No review comments found.")

if __name__ == "__main__":
    main()
