{
	exception Eof;;
}

rule token = parse
	| [' ' '\t' '\n'] 
		{ token lexbuf }
	| ['1'-'9'] ['0'-'9']* as nn
		{ Genlex.Int (int_of_string nn) }
	| ['\"']
		{ let ss = getString lexbuf
		  in
		  Genlex.String ss
		}
	| ['0'-'9' 'A'-'Z' 'a'-'z' '|' '_' '-' '[' ']' '*']+ as ss
		{ Genlex.Ident ss }
	| ['=' '(' ')' ',' '!' '.'] as kwd
		{ Genlex.Kwd (String.make 1 kwd) }
	| eof
		{ raise Eof }
and getString = parse
	| ([^'\"']* as ss) ['\"']
		{ ss }

