import shutil

REQUIRED_TOOLS = {
    ("smtbmc", "yices"): ["yices-smt2"],
    ("smtbmc", "z3"): ["z3"],
    ("smtbmc", "cvc4"): ["cvc4"],
    ("smtbmc", "mathsat"): ["mathsat"],
    ("smtbmc", "boolector"): ["boolector"],
    ("smtbmc", "bitwuzla"): ["bitwuzla"],
    ("smtbmc", "abc"): ["yosys-abc"],
    ("aiger", "suprove"): ["suprove", "yices"],
    ("aiger", "avy"): ["avy", "yices"],
    ("aiger", "aigbmc"): ["aigbmc", "yices"],
    ("btor", "btormc"): ["btormc", "btorsim"],
    ("btor", "pono"): ["pono", "btorsim"],
    ("abc"): ["yices"],
}


if __name__ == "__main__":
    import subprocess
    import sys
    from pathlib import Path

    found_tools = []
    check_tools = set()
    for tools in REQUIRED_TOOLS.values():
        check_tools.update(tools)

    for tool in sorted(check_tools):
        if not shutil.which(tool):
            continue

        if tool == "btorsim":
            error_msg = subprocess.run(
                ["btorsim", "--vcd"],
                capture_output=True,
                text=True,
            ).stderr
            if "invalid command line option" in error_msg:
                print(
                    "found `btorsim` binary is too old "
                    "to support the `--vcd` option, ignoring"
                )
                continue

        found_tools.append(tool)

    found_tools = "\n".join(found_tools + [""])

    try:
        with open("make/rules/found_tools") as found_tools_file:
            if found_tools_file.read() == found_tools:
                exit(0)
    except FileNotFoundError:
        pass

    Path("make/rules").mkdir(exist_ok=True)

    with open("make/rules/found_tools", "w") as found_tools_file:
        found_tools_file.write(found_tools)
else:
    with open("make/rules/found_tools") as found_tools_file:
        found_tools = [tool.strip() for tool in found_tools_file.readlines()]