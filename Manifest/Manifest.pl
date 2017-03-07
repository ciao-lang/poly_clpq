:- bundle(poly_clpq).
% The default development environment
version('1.0').
alias_paths([
  library = 'lib'
]).
depends([
  core-[version>='1.16.0-alpha.3']
]).
lib('lib').
