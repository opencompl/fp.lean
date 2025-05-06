#!/usr/bin/env python3

import duckdb
import argparse
import sys
import os

# Helper for colored output
class Colors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

    @staticmethod
    def supports_color():
        """
        Returns True if the running system's terminal supports color,
        and False otherwise.
        From: https://stackoverflow.com/a/22254892
        """
        is_a_tty = hasattr(sys.stdout, 'isatty') and sys.stdout.isatty()
        return is_a_tty

# Disable colors if not supported
if not Colors.supports_color():
    for attr_name in dir(Colors):
        if attr_name.isupper(): # Heuristic: color codes are uppercase class attributes
            setattr(Colors, attr_name, "")


def main():
    parser = argparse.ArgumentParser(
        description="Compare reference golden (e.g. floatx-golden) against fplean-golden CSV files. \n"
                    "Checks that every row (based on op, mode, op1, op2) in the first file (e.g. floatx-golden) \n"
                    "exists in the second file (fplean-golden) with the same result column. \n"
                    "Reports mismatches grouped by rounding mode and operation type.",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument("floatx_golden_path", help="Path to the floatx-golden CSV file (expected values).")
    parser.add_argument("fplean_golden_path", help="Path to the fplean-golden CSV file (actual values).")
    args = parser.parse_args()

    fx_path = args.floatx_golden_path
    fp_path = args.fplean_golden_path

    if not os.path.exists(fx_path):
        print(f"{Colors.FAIL}Error: Expected values file not found at {fx_path}{Colors.ENDC}")
        sys.exit(2)
    if not os.path.exists(fp_path):
        print(f"{Colors.FAIL}Error: Actual values file not found at {fp_path}{Colors.ENDC}")
        sys.exit(2)

    # Column names based on the example: operation, rounding_mode, operand1, operand2, result
    # Ensure this list of strings is correctly formatted for the SQL query
    col_names_list_str = "['operation', 'rounding_mode', 'operand1', 'operand2', 'result']"

    con = None # Initialize con to None for the finally block
    try:
        con = duckdb.connect(database=':memory:', read_only=False)

        # The query joins floatx (fx) with fplean (fp) on the input columns.
        # We are looking for rows in floatx where:
        # 1. The input combination (op, rm, op1, op2) does NOT exist in fplean
        #    (fp.operation IS NULL after LEFT JOIN)
        # OR
        # 2. The input combination exists, but the result is different (fx.result != fp.result)
        query = f"""
        SELECT
            fx.operation,
            fx.rounding_mode,
            fx.operand1,
            fx.operand2,
            fx.result AS expected_result,
            fp.result AS actual_result  -- This will be NULL if the input combo wasn't in fplean
        FROM
            read_csv_auto('{fx_path}', names={col_names_list_str}, header=False, all_varchar=true) AS fx
        LEFT JOIN
            read_csv_auto('{fp_path}', names={col_names_list_str}, header=False, all_varchar=true) AS fp
        ON
            fx.operation = fp.operation AND
            fx.rounding_mode = fp.rounding_mode AND
            fx.operand1 = fp.operand1 AND
            fx.operand2 = fp.operand2
        WHERE
            fp.operation IS NULL OR fx.result != fp.result -- Mismatch condition
        ORDER BY
            fx.rounding_mode, fx.operation, fx.operand1, fx.operand2;
        """
        # print(f"Debug SQL Query:\n{query}") # For debugging

        mismatches = con.execute(query).fetchall()

    except Exception as e:
        print(f"{Colors.FAIL}An error occurred during DuckDB processing: {e}{Colors.ENDC}")
        sys.exit(3)
    finally:
        if con:
            con.close()

    if mismatches:
        print(f"{Colors.FAIL}{Colors.BOLD}Mismatches found:{Colors.ENDC}")
        current_rm = None
        current_op = None

        fx_basename = os.path.basename(fx_path)
        fp_basename = os.path.basename(fp_path)

        for row_idx, row_data in enumerate(mismatches):
            op, rm, op1, op2, expected, actual = row_data

            if rm != current_rm or op != current_op:
                if current_rm is not None: # Print a newline between groups
                    print()
                print(f"{Colors.HEADER}--- Group: Rounding Mode = {Colors.BOLD}{rm}{Colors.ENDC}{Colors.HEADER}, Operation = {Colors.BOLD}{op}{Colors.ENDC}{Colors.HEADER} ---{Colors.ENDC}")
                current_rm = rm
                current_op = op

            if actual is None: # This means the input combination was not found in fplean-golden
                actual_display = f"{Colors.FAIL}{Colors.BOLD}NOT FOUND in {fp_basename}{Colors.ENDC}"
            else: # Input combination found, but result differs
                actual_display = f"{Colors.FAIL}{actual}{Colors.ENDC}"

            print(f"  Mismatch for inputs: (op1={Colors.OKBLUE}{op1}{Colors.ENDC}, op2={Colors.OKBLUE}{op2}{Colors.ENDC})")
            print(f"    Expected (from {fx_basename}): {Colors.OKGREEN}{expected}{Colors.ENDC}")
            print(f"    Actual   (from {fp_basename}):   {actual_display}")

        print(f"\n{Colors.FAIL}{Colors.BOLD}Found {len(mismatches)} mismatch(es). Script FAILED.{Colors.ENDC}")
        sys.exit(1)
    else:
        print(f"{Colors.OKGREEN}{Colors.BOLD}All checks passed. No mismatches found between {os.path.basename(fx_path)} and {os.path.basename(fp_path)}.{Colors.ENDC}")
        sys.exit(0)

if __name__ == "__main__":
    main()
