exception NotFound of string

datatype expression = 
	 	Var of string
	| Num of int 
	| Boolean of bool
	| Lambda of string*expression
  | App of expression*expression
	| Add of expression*expression
	| Sub of expression*expression
	| Mul of expression*expression
	| Div of expression*expression
	| Lesser of expression*expression
	| Greater of expression*expression
	| Lequal of expression*expression
	| Gequal of expression*expression
	| Equal of expression*expression
	| If_else of expression*expression*expression
	| Let_in of string*expression*expression
	| And of expression*expression
	| Or of expression*expression

and closure = 
 		 Closure of expression * ((string*closure) list)

and ans = 
			Int of int
			| Bool of bool
			| Fun of string*expression*((string*closure) list)

type stack = closure list

fun lookup (x,[]) = raise NotFound x
	|	lookup (x,(y,z)::ls) = if (x=y) then z else lookup(x,ls)

fun 
		execute (Closure(Num(x),env),s:stack) 		 = Int(x)
	| execute (Closure(Boolean(x),env),s:stack)  = Bool(x)
	|	execute (Closure(Var(x),env),s:stack) 		 = (let val y = lookup(x,env) in execute(y,s) end)
	| execute	(Closure(Lambda(x,e),env),[])			 = Fun(x,e,env)
	| execute	(Closure(Lambda(x,e),env),s:stack) = (let val c = hd(s); val y = (x,c) in execute(Closure(e,y::env),tl(s)) end)
	| execute	(Closure(App(m,n),env),s:stack) 	 = (let val a = Closure(m,env) ; val b = Closure(n,env) in execute(a,b::s) end)	
	|	execute	(Closure(Add(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Int(a+b) end)
	|	execute	(Closure(Sub(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Int(a-b) end)
	|	execute	(Closure(Mul(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Int(a*b) end)
	|	execute	(Closure(Div(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Int(Int.div(a,b)) end)
	|	execute	(Closure(Lesser(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Bool(a<b) end)
	|	execute	(Closure(Greater(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Bool(a>b) end)
	|	execute	(Closure(Lequal(e1,e2),env),s:stack)  = 
    (let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Bool(a<=b) end)
	|	execute	(Closure(Gequal(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Bool(a>=b) end)
	|	execute	(Closure(Equal(e1,e2),env),s:stack)  = 
		(let val Int(a) = execute(Closure(e1,env),s); val Int(b) = execute(Closure(e2,env),s) in Bool(a=b) end)
	|	execute	(Closure(If_else(e1,e2,e3),env),s:stack)  = 
		(let 
				val Bool(cond) = execute(Closure(e1,env),s); 
			in 
				if(cond) then execute(Closure(e2,env),s) 
			  else execute(Closure(e3,env),s)
		 end)
	|	execute	(Closure(Let_in(x,e1,e2),env),s:stack)  = 
		(let 
				val env_ = (x,Closure(e1,env))::env ;
				val y 	 = Closure(e2,env_)
			in 
				execute(y,s)
		 end)
	|	execute	(Closure(And(e1,e2),env),s:stack)  = 
		(let val Bool(a) = execute(Closure(e1,env),s); val Bool(b) = execute(Closure(e2,env),s) in Bool(a andalso b) end)
	|	execute	(Closure(Or(e1,e2),env),s:stack)  = 
		(let val Bool(a) = execute(Closure(e1,env),s); val Bool(b) = execute(Closure(e2,env),s) in Bool(a orelse b) end)


(* test cases
val exp1 = App(Lambda("x",Var("x")),Num(3));
val exp2 = App(Lambda("x",Add(App(Lambda("y",Mul(Var("y"),Sub(Num(1),Var("y")))),Num(3)),Var("x"))),Num(1));
val condition = App(Lambda("x",Boolean(false)),Lambda("c",Num(1)));
val if_ = App(Lambda("x",Add(App(Lambda("y",Mul(Var("y"),Sub(Num(1),Var("y")))),Num(3)),Var("x"))),Num(10));
val el = Num(10);
val exp3 = If_else(condition,if_,el);
val exp4 = Let_in("x",Num(3),Let_in("y",Num(4),Add(Var("y"),Var("x"))));
val exp5 = Lambda("x",Add(Num(4),Var("x")));

val ans1 = execute(Closure(exp1,[]),[]);
val ans2 = execute(Closure(exp2,[]),[]);
val ans3 = execute(Closure(exp3,[]),[]);
val ans4 = execute(Closure(exp4,[]),[]);
val ans5 = execute(Closure(exp5,[]),[]);
*)
