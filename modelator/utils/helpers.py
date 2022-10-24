# removes the prefix `prefix` from `text`.
# Implemented here as a helper fucntion in order to support Python 3.8
def remove_prefix(text, prefix):
    if text.startswith(prefix):
        return text[len(prefix) :]
    return text
