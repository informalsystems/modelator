from modelator.ModelResult import ModelResult


class ModelMonitor:
    """
    Monitor for actions done with the model
    """

    def on_parse_start(self, res: ModelResult):
        pass

    def on_parse_finish(self, res: ModelResult):
        pass

    def on_sample_start(self, res: ModelResult):
        pass

    def on_sample_update(self, res: ModelResult):
        pass

    def on_sample_finish(self, res: ModelResult):
        pass

    def on_check_start(self, res: ModelResult):
        pass

    def on_check_update(self, res: ModelResult):
        pass

    def on_check_finish(self, res: ModelResult):
        pass
