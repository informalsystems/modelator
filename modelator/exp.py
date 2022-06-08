from modelator.Model import Model

# from Model import Model


def main():

    m = Model.parse_file("modelator/samples/Hello.tla")
    print(m.variables)
    m.typecheck()


if __name__ == "__main__":
    main()
