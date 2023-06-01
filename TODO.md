# List Of To Dos!

## General (low priority)
- [x] create requirements file
- [ ] add word boundary handling for generator / test for data
- [ ] add no context handling for generator
- [x] add rule interaction generation
- [ ] make new .yml file that reduces prague overload

## Algorithmic (high priority)
- [ ] generate datasets
  - [ ] have it spit out metadata
  - [ ] also have it more robust as far as creating rule interaction, give it more args
- [ ] make sure rules are numbered
- [ ] implement infering one rule
  - NOTE: format correctly
- [ ] implement combining rules (put in correct spot)
- [ ] implement checking rules pairwise
- [ ] implement generating new surface forms (from og, not intermediate)
- [ ] implement iteration

## Questions
How to make __init__.py pretty?

Are either of these correct?

`conda env create -name phonologica -f prague/prague_env.yml` 

`conda env update --name phonologica --file requirements.txt --prune`