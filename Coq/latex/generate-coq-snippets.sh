# For information about how this works, see: README-for-generating-Coq-snippets.md

python ./driver.py --frontend coq --backend snippets-hydras --output-directory coq-snippets ../VeracityLogic.v
python ./driver.py --frontend coq --backend assets --output-directory coq-snippets/assets -