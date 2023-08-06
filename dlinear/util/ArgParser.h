#ifndef DLINEAR5_ARGPARSER_H
#define DLINEAR5_ARGPARSER_H

#include <iostream>
#include <string>
#include <argparse/argparse.hpp>
#include "dlinear/util/Config.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/logging.h"

#ifndef PROG_NAME
#define PROG_NAME "dlinear"
#endif
#ifndef PROG_VERSION
#define PROG_VERSION "0.0.1"
#endif


using std::string;
using std::ostream;
using std::endl;
using std::cerr;

namespace dlinear {

    class ArgParser {
    private:
        argparse::ArgumentParser parser_;

        void addOptions();

    public:
        ArgParser();

        void parse(int argc, const char **argv);

        friend ostream &operator<<(ostream &os, const ArgParser &parser);

        [[nodiscard]] Config toConfig() const;

        template<typename T = std::string>
        [[nodiscard]] T get(const std::string &key) const { return parser_.get<T>(key); }

        friend ostream &operator<<(ostream &os, const dlinear::ArgParser &parser);
    };

} // dlinear



#endif //DLINEAR5_ARGPARSER_H
