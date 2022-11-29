# Installation

To install and use Modelator, make sure your system has

- `Python 3.8` or newer
- `Java 17` or newer

## Python

Installing Modelator requires [Python](https://www.python.org) 3.8 or newer, together with its package manager [pip](https://pip.pypa.io/en/stable/installation/).
(They come pre-installed on Linux and MacOS.)

A good tool for managing different python versions is [pyenv](<(https://github.com/pyenv/pyenv)>).
For example:

```
pyenv install 3.10.6
pyenv global 3.10.6
```

These two commands set the python version to 3.10.6. If you want to go back to your old Python version, run `pyenv global system`.
(For the Python version to be changed only in a current working directory, use the analogous `pyenv local...` command.)

Once you have the correct version of Python, run `pip install modelator`.
That's it! Please verify that the tool is working by writing `modelator` on the command line.
You should see something like this:

![Modelator CLI](docs/images/modelator_cli.png)

## Java

Modelator uses our in-house Apalache model checker to generate test scenarios from TLA+ models.

Modelator allows you to download and manage Apalache releases automatically, so you don't need to worry about that. The only prerequisite for using Apalache is to have Java installed on your system. We recommend version 17 builds of OpenJDK, for example [Eclipse Temurin](https://adoptium.net/) or [Zulu](https://www.azul.com/downloads/?version=java-17-lts&package=jdk#download-openjdk). In case you don't have Java installed already, please download and install the package suitable for your system.
