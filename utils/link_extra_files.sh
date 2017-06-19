#!/bin/bash
pushd .
cd ../z3/src/smt
ln -sf ../../../new_files/smt_model_reporter.cpp smt_model_reporter.cpp
ln -sf ../../../new_files/theory_special_relations.cpp theory_special_relations.cpp
ln -sf ../../../new_files/theory_special_relations.h theory_special_relations.h
popd
pushd .
cd ../z3/src/ast
ln -sf ../../../new_files/special_relations_decl_plugin.cpp special_relations_decl_plugin.cpp
ln -sf ../../../new_files/special_relations_decl_plugin.h special_relations_decl_plugin.h
popd
pushd .
cd ../z3/src/api
ln -sf ../../../new_files/api_special_relations.cpp api_special_relations.cpp
popd