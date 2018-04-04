exception NotFound of string

datatype expression = 
	 	Var of string
	| Num of int 
	| Boolean of bool
	| Add of expression*expression
	| Div of expression*expression
  | Sub of expression*expression
  | Mul of expression*expression
  | Lambda of string*expression
  | App of expression*expression
	| If_else of expression*expression*expression
  | Def of string*expression
  | Let_in of expression list * expression
	|	Lesser of expression * expression
	|	Lequal	of expression * expression
	|	Greater of expression * expression
	|	Gequal of expression * expression
	|	Equal of expression * expression
	| And of expression * expression
	| Or of expression * expression
	| Tuple of expression list
	
and opcode =
	 	CONST	of int
	| BOOL of bool
	|	LOOKUP of string
	|	CLOSURE of string * (opcode list)
	| DEF of string  	
	| IF_ELSE 	
	| APP  
	| RET 
	| ADD 
	| SUB 
	| MUL 
	| DIV
 	| LET  
  | IN
	| LT
	| LTE
	| GTE
	| GT
	| EQUAL
	| AND 
	| OR
	| TUPLE of int

and value = 
 		  Int of int
		| Bool of bool
    | Closure of ((string * value) list) * string * (opcode list)
    | SDef of string*value
		| T of value list

type ans = string * value

type stack = value list

type env 	= ans list

type code = opcode list

type dump	= stack*env*code

fun lookup (x,[]) = raise NotFound x
	|	lookup (x,(y,z)::ls) = if (x=y) then z else lookup(x,ls)

fun compile (Var(x)) 			= [LOOKUP(x)]
	| compile (Num(x)) 			= [CONST(x)]
	| compile (Boolean(x))	= [BOOL(x)]
	| compile (Lambda(x,e)) = [CLOSURE(x,compile(e))]
	| compile (App(e1,e2)) 	= compile(e1)@compile(e2)@[APP]
	| compile (Add(e1,e2)) 	= compile(e1)@compile(e2)@[ADD]
	| compile (Sub(e1,e2))	=	compile(e1)@compile(e2)@[SUB]
	| compile (Mul(e1,e2)) 	=	compile(e1)@compile(e2)@[MUL]
	| compile (Div(e1,e2)) 	=	compile(e1)@compile(e2)@[DIV]
	| compile (Lesser(e1,e2)) =	compile(e1)@compile(e2)@[LT]
	| compile (Greater(e1,e2)) = compile(e1)@compile(e2)@[GT]
	| compile (Lequal(e1,e2)) =	compile(e1)@compile(e2)@[LTE]
	| compile (Gequal(e1,e2)) =	compile(e1)@compile(e2)@[GTE]
	| compile (Equal(e1,e2)) =	compile(e1)@compile(e2)@[EQUAL]
	| compile (And(e1,e2)) =	compile(e1)@compile(e2)@[AND]
	| compile (Or(e1,e2)) =	compile(e1)@compile(e2)@[OR]	
	| compile	(If_else(e1,e2,e3)) = compile(e1)@compile(e2)@compile(e3)@[IF_ELSE]
  | compile	(Def(e1,e2)) = compile(e2)@[DEF(e1)]
  | compile (Let_in(ls,e)) = ( let
                                     fun help [] = []
                                       | help (x::xs) = compile(x)@help(xs)
                               in
                                      [LET]@help(ls)@[IN]@compile(e)@[RET]
                               end )
	| compile	(Tuple(ls)) = (let 
														val myls = (List.foldl (fn (a,b) => b@compile(a)) [] ls);
														val len = List.length(myls);
													in		
														myls@[TUPLE(len)]
													end)				

fun execute (s:stack,e:env,[],d:dump list) = hd(s)
	|	execute (s:stack,e:env,c:code,d:dump list) =
case hd(c) of 
		CONST(x) 						=>	let val y = Int(x) in execute(y::s,e,tl(c),d) end  
	| BOOL(x)							=> 	let val y = Bool(x) in execute(y::s,e,tl(c),d) end
	|	LOOKUP(x)					 	=>	let val y = lookup(x,e) in execute(y::s,e,tl(c),d) end 
	| CLOSURE(var,oplist) =>	let val y = Closure(e,var,oplist) in execute(y::s,e,tl(c),d) end 
	| APP 			 					=>
		(let 
				val a2 = hd(s); 
				val Closure(x,y,z) = hd(tl(s)); 
				val binding = (y,a2) 
		in 
			execute([],binding::e,z@[RET],((tl(tl(s)),e,tl(c))::d)) 
		end)  
	| RET 								=>	let val (ss,ee,cc) = hd(d) in execute(hd(s)::ss,ee,cc,tl(d)) end
	| ADD 								=>	(let val Int(e1) = hd(s); val Int(e2) = hd(tl(s)); val ans=Int(e1+e2) in execute(ans::s,e,tl(c),d) end)
	| SUB 								=>	(let val Int(e1) = hd(s); val Int(e2) = hd(tl(s)); val ans=Int(e2-e1) in execute(ans::s,e,tl(c),d) end)
	| MUL 								=>	(let val Int(e1) = hd(s); val Int(e2) = hd(tl(s)); val ans=Int(e2*e1) in execute(ans::s,e,tl(c),d) end)
	| DIV 								=>	(let val Int(e1) = hd(s); val Int(e2) = hd(tl(s)); val ans=Int(Int.div(e2,e1)) in execute(ans::s,e,tl(c),d) end)
 	| IF_ELSE 						=>	
		(let
				val e2::e1::(Bool(cond))::t = s;
		in
				if cond then execute(e1::t,e,tl(c),d) 
				else execute(e2::t,e,tl(c),d)
		end)
   | DEF(x)             =>  (let val y = hd(s) in execute(s,(x,y)::e,tl(c),d) end) 
   | LET                =>  execute(s,e,tl(c),(s,e,tl(c))::d)
   | IN                 =>  (let 
                                val (s1,e1,c1) = hd(d);
																fun f(clist) = if hd(clist)=RET then tl(clist) 
																							 else f(tl(clist));
																val opClist =  f(c);
														 in
																execute([],e,tl(c),(s1,e1,opClist)::tl(d))
														end)
	| LT		=>	(let val Int(e2) = hd(s); val Int(e1) = hd(tl(s)); val ans=Bool(op<(e1,e2)) in execute(ans::s,e,tl(c),d) end)	
	| GT		=>	(let val Int(e2) = hd(s); val Int(e1) = hd(tl(s)); val ans=Bool(op>(e1,e2)) in execute(ans::s,e,tl(c),d) end)	
	| LTE		=>	(let val Int(e2) = hd(s); val Int(e1) = hd(tl(s)); val ans=Bool(op<=(e1,e2)) in execute(ans::s,e,tl(c),d) end)
	| GTE		=>	(let val Int(e2) = hd(s); val Int(e1) = hd(tl(s)); val ans=Bool(op>=(e1,e2)) in execute(ans::s,e,tl(c),d) end)	
	| EQUAL	=>	(let val Int(e2) = hd(s); val Int(e1) = hd(tl(s)); val ans=Bool(e1=e2) in execute(ans::s,e,tl(c),d) end)	
	| AND		=>	(let val Bool(e1) = hd(s); val Bool(e2) = hd(tl(s)); val ans=Bool(e1 andalso e2) in execute(ans::s,e,tl(c),d) end)
	| OR		=>	(let val Bool(e1) = hd(s); val Bool(e2) = hd(tl(s)); val ans=Bool(e1 orelse e2) in execute(ans::s,e,tl(c),d) end)
	| TUPLE(n) =>
	(let
			val a = T(List.take(s,n));
			val ss = a::(List.drop(s,n));
	 in
			execute(ss,e,tl(c),d) 
	end)
	

val exp1 = App(Lambda("x",Add(Var("x"),Num(3))),Num(5));
val exp2 = App(Lambda("x",Add(App(Lambda("y",Mul(Var("y"),Sub(Num(1),Var("y")))),Num(3)),Var("x"))),Num(1));
val exp3 = Let_in([Def("x",Num(1))],Var("x"));
val exp4 = If_else(Boolean(false),Num(7),Num(8));
val condition = App(Lambda("x",Boolean(false)),Lambda("c",Num(1)));
val if_ = App(Lambda("x",Add(App(Lambda("y",Mul(Var("y"),Sub(Num(1),Var("y")))),Num(3)),Var("x"))),Num(10));
val el = Num(10);
val exp5 = If_else(condition,if_,el);
val exp6 = Let_in([Def("x",Num(5)),Def("y",Num(6))],Add(Var("x"),Var("y")));
val exp7 = Lambda("x",Add(Num(4),Var("x")));


val b1 = Lesser(Num(2),Num(3));
val b2 = Greater(Num(2),Num(3));
val b3 = Lequal(Num(2),Num(3));
val b4 = Gequal(Num(2),Num(3));
val b5 = Equal(Num(2),Num(3));
val codelistb1 = compile(b1);
val codelistb2 = compile(b2);
val codelistb3 = compile(b3);
val codelistb4 = compile(b4);
val codelistb5 = compile(b5);

val codelist1 = compile(exp1);
val codelist2 = compile(exp2);
val codelist3 = compile(exp3);
val codelist4 = compile(exp4);
val codelist5 = compile(exp5);
val codelist6 = compile(exp6);
val codelist7 = compile(exp7);


val ans1 = execute([],[],codelist1,[]);
val ans2 = execute([],[],codelist2,[]);
val ans3 = execute([],[],codelist3,[]);
val ans4 = execute([],[],codelist4,[]);
val ans5 = execute([],[],codelist5,[]);
val ans6 = execute([],[],codelist6,[]);
val ans7 = execute([],[],codelist7,[]);

val ansb1 = execute([],[],codelistb1,[]);
val ansb2 = execute([],[],codelistb2,[]);
val ansb3 = execute([],[],codelistb3,[]);
val ansb4 = execute([],[],codelistb4,[]);
val ansb5 = execute([],[],codelistb5,[]);

