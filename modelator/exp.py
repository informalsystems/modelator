from modelator.Model import Model

# from Model import Model


def main():

    m = Model.parse_file("modelator/samples/Hello.tla")
    m.typecheck()


if __name__ == "__main__":
    main()
