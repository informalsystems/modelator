// cbindgen --lang=c

typedef struct CResult {
  char *data;
  char *error;
} CResult;

struct CResult generate_json_traces_from_tla_tests_rs(const char *tla_tests_file_path_c,
                                                      const char *tla_config_file_path_c);
