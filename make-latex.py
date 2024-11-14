import os
import shutil
import subprocess

def convert_to_lagda_and_compile(dir):
    for filename in os.listdir(dir):
        filepath = os.path.join(dir, filename)
        if os.path.isfile(filepath) and filepath.endswith(".agda"):
            # Copy file contents and delete
            agda_lines = [line for line in open(filepath)]
            new_filepath = filepath.replace(".agda", ".lagda")
            os.remove(filepath)

            # Create new, empty file
            if os.path.exists(new_filepath):
                os.remove(new_filepath)
            with open(new_filepath, "w") as f:
                content = ["\\begin{code}"] + agda_lines + ["\\end{code}"]
                f.write("\n".join(content))

            # Do compilation
            command = f"agda --latex --only-scope-checking {new_filepath}"
            try:
                subprocess.run(command, shell=True, check=True)
            except subprocess.CalledProcessError as e:
                print(f"Error executing {command}: {e}")


def compile_agda_project(dir, output):
    output = os.path.abspath(output)

    # Create temporary directory 
    tempdir = f"{dir}-temp"
    shutil.copytree(dir, tempdir)

    cwd = os.getcwd()
    # Change cwd into src directory first, then change back
    os.chdir(tempdir)
    convert_to_lagda_and_compile("src")
    os.chdir(cwd)

    # Having trouble with setting output directory, so manually copy
    output_dir = os.path.join(tempdir, "latex")
    for filename in os.listdir(output_dir):
        filepath = os.path.join(output_dir, filename)
        shutil.copy2(filepath, output)

    # Cleanup
    shutil.rmtree(tempdir)

os.makedirs("latex/moggi", exist_ok=True)
compile_agda_project("moggi", "latex/moggi")
os.makedirs("latex/fitch", exist_ok=True)
compile_agda_project("fitch", "latex/fitch")