import subprocess

def main():
    for i in range(1, 16):
        command = "git checkout a{}".format(i) + " && " + "git checkout master -- build/build.py" + " && " + "git add . && git commit -m \"update build.py\""
        pro = subprocess.Popen(command, shell = True)
        _ = pro.communicate()

if __name__ == "__main__":
    main()