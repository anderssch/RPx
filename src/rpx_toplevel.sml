(* ========================================================================= *)
(* RPx prover extended with TPTP parsing                                     *)
(* Copyright (c) 2018 Anders Schlichtkrull, Jasmin Christian Blanchette,     *)
(*                    Dmitriy Traytel                                        *)
(*                                                                           *)
(* TPTP parsing and clausification adapted from                              *)
(* METIS FIRST ORDER PROVER                                                  *)
(* Copyright (c) 2001 Joe Leslie-Hurd, distributed under the MIT license     *)
(* ========================================================================= *)

open Useful;

(* ------------------------------------------------------------------------- *)
(* The program name and version.                                             *)
(* ------------------------------------------------------------------------- *)

val PROGRAM = "RPx";

val VERSION = "X.Z";

val versionString = PROGRAM^" "^VERSION^" (release 2019ZZZZ)"^"\n";

(* ------------------------------------------------------------------------- *)
(* Program options.                                                          *)
(* ------------------------------------------------------------------------- *)

val ITEMS = ["name","goal","clauses","size","category","proof","saturation"];

val TIMEOUT : int option ref = ref NONE;

val TPTP : string option ref = ref NONE;

val QUIET = ref false;

val TEST = ref false;

val extended_items = "all" :: ITEMS;

val show_items = List.map (fn s => (s, ref false)) ITEMS;

fun show_ref s =
    case List.find (equal s o fst) show_items of
      NONE => raise Bug ("item " ^ s ^ " not found")
    | SOME (_,r) => r;

fun show_set b = app (fn (_,r) => r := b) show_items;

fun showing s = not (!QUIET) andalso (s = "status" orelse !(show_ref s));

fun notshowing s = not (showing s);

fun showing_any () = List.exists showing ITEMS;

fun notshowing_any () = not (showing_any ());

fun show "all" = show_set true
  | show s = case show_ref s of r => r := true;

fun hide "all" = show_set false
  | hide s = case show_ref s of r => r := false;

(* ------------------------------------------------------------------------- *)
(* Process command line arguments and environment variables.                 *)
(* ------------------------------------------------------------------------- *)


  open Useful Options;

  val specialOptions =
    [(*{switches = ["--show"], arguments = ["ITEM"],
      description = "show ITEM (see below for list)",
      processor =
        beginOpt (enumOpt extended_items endOpt) (fn _ => fn s => show s)},
     {switches = ["--hide"], arguments = ["ITEM"],
      description = "hide ITEM (see below for list)",
      processor =
        beginOpt (enumOpt extended_items endOpt) (fn _ => fn s => hide s)},
     {switches = ["--time-limit"], arguments = ["N"],
      description = "give up after N seconds",
      processor =
        beginOpt (optionOpt ("-", intOpt (SOME 0, NONE)) endOpt)
          (fn _ => fn n => TIMEOUT := n)},
     {switches = ["--tptp"], arguments = ["DIR"],
      description = "specify the TPTP installation directory",
      processor =
        beginOpt (stringOpt endOpt) (fn _ => fn s => TPTP := SOME s)},
     {switches = ["-q","--quiet"], arguments = [],
      description = "Run quietly; indicate provability with return value",
      processor = beginOpt endOpt (fn _ => QUIET := true)},
     {switches = ["--test"], arguments = [],
      description = "Skip the proof search for the input problems",
      processor = beginOpt endOpt (fn _ => TEST := true)}*)];


val programOptions =
    {name = PROGRAM,
     version = versionString,
     header = "usage: "^PROGRAM^" [option ...] problem.tptp ...\n" ^
              "Proves the input TPTP problem files.\n",
     footer = "Possible ITEMs are {" ^ join "," extended_items ^ "}.\n" ^
              "Problems can be read from standard input using the " ^
              "special - filename.\n",
     options = specialOptions @ Options.basicOptions};

fun exit x : unit = Options.exit programOptions x;
fun succeed () = Options.succeed programOptions;
fun fail mesg = Options.fail programOptions mesg;
fun usage mesg = Options.usage programOptions mesg;

fun processOptions () =
    (let
      val args = CommandLine.arguments ()

      val (_,work) = Options.processOptions programOptions args

      val () =
          case !TPTP of
            SOME _ => ()
          | NONE => TPTP := OS.Process.getEnv "TPTP"
    in
      work
    end);

(* ------------------------------------------------------------------------- *)
(* The core application.                                                     *)
(* ------------------------------------------------------------------------- *)

fun newLimit () =
    case !TIMEOUT of
      NONE => K true
    | SOME lim =>
      (let
        val timer = Timer.startRealTimer ()

        val lim = Time.fromReal (Real.fromInt lim)

        fun check () =
            (let
              val time = Timer.checkRealTimer timer
            in
              Time.<= (time,lim)
            end)
      in
        check
      end);


val next_cnf =
    (let
      val cnf_counter = ref 0
    in
      fn () =>
         (let
           val ref cnf_count = cnf_counter
           val () = cnf_counter := cnf_count + 1
         in
           cnf_count
         end)
    end);



  fun display_sep () =
      if notshowing_any () then ()
      else TextIO.print (nChars #"%" (!Print.lineLength) ^ "\n");

  fun display_name filename =
      if notshowing "name" then ()
      else TextIO.print ("Problem: " ^ filename ^ "\n\n");

  fun display_goal tptp =
      if notshowing "goal" then ()
      else
        (let
          val goal = Tptp.goal tptp
        in
          TextIO.print ("Goal:\n" ^ Formula.toString goal ^ "\n\n")
        end);

  fun display_clauses cls =
      if notshowing "clauses" then ()
      else TextIO.print ("Clauses:\n" ^ Problem.toString cls ^ "\n\n");

  fun display_size cls =
      if notshowing "size" then ()
      else
        (let
          fun plural 1 s = "1 " ^ s
            | plural n s = Int.toString n ^ " " ^ s ^ "s"

          val {clauses,literals,symbols,typedSymbols} = Problem.size cls
        in
          TextIO.print
            ("Size: " ^
             plural clauses "clause" ^ ", " ^
             plural literals "literal" ^ ", " ^
             plural symbols "symbol" ^ ", " ^
             plural typedSymbols "typed symbol" ^ ".\n\n")
        end);

  fun display_category cls =
      if notshowing "category" then ()
      else
        (let
          val cat = Problem.categorize cls
        in
          TextIO.print ("Category: " ^ Problem.categoryToString cat ^ ".\n\n")
        end);


    fun display_proof_start filename =
        TextIO.print ("\n% SZS output start CNFRefutation for " ^ filename ^ "\n");

    fun display_proof_body problem proofs =
        (let
          val comments = []

          val includes = []

          val formulas =
              Tptp.fromProof
                {problem = problem,
                 proofs = proofs}

          val proof =
              Tptp.Problem
                {comments = comments,
                 includes = includes,
                 formulas = formulas}

          val mapping = Tptp.defaultMapping
          val mapping = Tptp.addVarSetMapping mapping (Tptp.freeVars proof)

          val filename = "-"
        in
          Tptp.write
            {problem = proof,
             mapping = mapping,
             filename = filename}
        end);

    fun display_proof_end filename =
        TextIO.print ("% SZS output end CNFRefutation for " ^ filename ^ "\n\n");

    fun display_proof filename problem proofs =
        if notshowing "proof" then ()
        else
          (let
            val () = display_proof_start filename
            val () = display_proof_body problem proofs
            val () = display_proof_end filename
          in
            ()
          end);

  fun display_saturation filename ths =
      if notshowing "saturation" then ()
      else
        (let
          val () =
              (let
                val problem =
                    Tptp.mkProblem
                      {comments = ["Saturation clause set for " ^ filename],
                       includes = [],
                       names = Tptp.noClauseNames,
                       roles = Tptp.noClauseRoles,
                       problem = {axioms = [],
                                  conjecture = List.map Thm.clause ths}}

                val mapping =
                    Tptp.addVarSetMapping Tptp.defaultMapping
                      (Tptp.freeVars problem)
              in
                Tptp.write
                  {problem = problem,
                   mapping = mapping,
                   filename = "saturation.tptp"}
              end)

          val () =
              TextIO.print
                ("\nSZS output start Saturation for " ^ filename ^ "\n")

          val () = app (fn th => TextIO.print (Thm.toString th ^ "\n")) ths

          val () =
              TextIO.print
                ("SZS output end Saturation for " ^ filename ^ "\n\n")
        in
          ()
        end);

  fun display_status filename status =
      if (*notshowing "status"*) false then ()
      else
        TextIO.print ("% SZS status " ^ Tptp.toStringStatus status ^
                      " for " ^ filename ^ "\n");

  fun display_problem filename cls =
      (let
        val () =
            (let
              val problem =
                  Tptp.mkProblem
                    {comments = ["CNF clauses for " ^ filename],
                     includes = [],
                     names = Tptp.noClauseNames,
                     roles = Tptp.noClauseRoles,
                     problem = cls}

              val mapping =
                  Tptp.addVarSetMapping Tptp.defaultMapping
                    (Tptp.freeVars problem)

              val filename = "cnf_" ^ Int.toString (next_cnf ()) ^ ".tptp"
            in
              () (*Tptp.write
                {problem = problem,
                 mapping = mapping,
                 filename = filename} *)
            end)

        val () = display_clauses cls

        val () = display_size cls

        val () = display_category cls
      in
        ()
      end);

  fun mkTptpFilename filename =
      if isPrefix "/" filename then filename
      else
        case !TPTP of
          NONE => filename
        | SOME tptp =>
          (let
            val tptp = stripSuffix (equal #"/") tptp
          in
            tptp ^ "/" ^ filename
          end);

  fun readIncludes mapping seen formulas includes =
      case includes of
        [] => formulas
      | inc :: includes =>
        if StringSet.member inc seen then
          readIncludes mapping seen formulas includes
        else
          (let
            val seen = StringSet.add seen inc

            val filename = mkTptpFilename inc

            val Tptp.Problem {includes = i, formulas = f, ...} =
                Tptp.read {filename = filename, mapping = mapping}

            val formulas = f @ formulas

            val includes = List.revAppend (i,includes)
          in
            readIncludes mapping seen formulas includes
          end);

  fun read mapping filename =
      (let
        val problem = Tptp.read {filename = filename, mapping = mapping}

        val Tptp.Problem {comments,includes,formulas} = problem
      in
        if List.null includes then problem
        else
          (let
            val seen = StringSet.empty

            val includes = List.rev includes

            val formulas = readIncludes mapping seen formulas includes
          in
            Tptp.Problem
              {comments = comments,
               includes = [],
               formulas = formulas}
          end)
      end);

  val resolutionParameters =
      (let
        val {active,waiting} = Resolution.default

        val waiting =
            (let
              val {symbolsWeight,
                   variablesWeight,
                   literalsWeight,
                   models} = waiting

              val models =
                  case models of
                    [{model = _,
                      initialPerturbations,
                      maxChecks,
                      perturbations,
                      weight}] =>
                    (let
                      val model = Tptp.defaultModel
                    in
                      [{model = model,
                        initialPerturbations = initialPerturbations,
                        maxChecks = maxChecks,
                        perturbations = perturbations,
                        weight = weight}]
                    end)
                  | _ => raise Bug "resolutionParameters.waiting.models"
            in
              {symbolsWeight = symbolsWeight,
               variablesWeight = variablesWeight,
               literalsWeight = literalsWeight,
               models = models}
            end)
      in
        {active = active,
         waiting = waiting}
      end);

  fun resolutionLoop limit res =
      case Resolution.iterate res of
        Resolution.Decided dec => SOME dec
      | Resolution.Undecided res =>
        if limit () then resolutionLoop limit res else NONE;

  fun refute limit {axioms,conjecture} =
      (let
        val axioms = List.map Thm.axiom axioms
        and conjecture = List.map Thm.axiom conjecture

        val problem = {axioms = axioms, conjecture = conjecture}

        val res = Resolution.new resolutionParameters problem
      in
        resolutionLoop limit res
      end);

  fun refuteAll limit filename tptp probs acc =
      case probs of
        [] =>
        (let
          val status =
              if !TEST then Tptp.UnknownStatus
              else if Tptp.hasFofConjecture tptp then Tptp.TheoremStatus
              else Tptp.UnsatisfiableStatus

          val () = display_status filename status

          val () =
              if !TEST then ()
              else display_proof filename tptp (List.rev acc)
        in
          true
        end)
      | prob :: probs =>
        (let
          val {subgoal,problem,sources} = prob

          val () = display_problem filename problem
        in
          if !TEST then refuteAll limit filename tptp probs acc
          else
            case refute limit problem of
              SOME (Resolution.Contradiction th) =>
              (let
                val subgoalProof =
                    {subgoal = subgoal,
                     sources = sources,
                     refutation = th}

                val acc = subgoalProof :: acc
              in
                refuteAll limit filename tptp probs acc
              end)
            | SOME (Resolution.Satisfiable ths) =>
              (let
                val status =
                    if Tptp.hasFofConjecture tptp then
                      Tptp.CounterSatisfiableStatus
                    else
                      Tptp.SatisfiableStatus

                val () = display_status filename status

                val () = display_saturation filename ths
              in
                false
              end)
            | NONE =>
              (let
                val status = Tptp.UnknownStatus

                val () = display_status filename status
              in
                false
              end)
        end);

  fun prove limit mapping filename =
      (let
        val () = display_sep ()

        val () = display_name filename

        val tptp = read mapping filename

        val () = display_goal tptp

        val problems = Tptp.normalize tptp
      in
        refuteAll limit filename tptp problems []
      end);

fun proveAll limit mapping filenames =
    List.all
      (if !QUIET then prove limit mapping
       else fn filename => prove limit mapping filename orelse true)
      filenames;


(** Glue code for RP prover **)

(* Extract clause *)
fun getFormulaBody (Tptp.Formula 
      {name = _,
       role = _,
       body = bod,
       source = _}) = bod;

fun clauseOfFormulaBody (Tptp.FofFormulaBody f) = List.concat (map LiteralSet.toList (Normalize.cnf f))
  | clauseOfFormulaBody (Tptp.CnfFormulaBody []) = []
  | clauseOfFormulaBody (Tptp.CnfFormulaBody (lit::ls)) =
       (case lit of
          Tptp.Literal l => l::(clauseOfFormulaBody (Tptp.CnfFormulaBody ls)) |
          Tptp.Boolean b => if b then [(true,(Name.fromString "p",[])),(false,(Name.fromString "p",[]))] 
                            else clauseOfFormulaBody (Tptp.CnfFormulaBody ls))

(* Convert to RP expressions *)
fun termOfTerm (Term.Var x) = RPx.Var ((Name.toString x)) |
    termOfTerm (Term.Fn (f,ts)) = RPx.Fun ((Name.toString f), map termOfTerm ts);
                                         
exception SZS_Status_Inappropriate

fun termOfAtm (r,ts) = if Name.toString r = "=" then raise SZS_Status_Inappropriate else RPx.Fun ((Name.toString r), map termOfTerm ts) 

fun litOfLit (p,a : Atom.atom) = (if p then RPx.Pos else RPx.Neg) (termOfAtm a);

fun clauseOfClause cls = map litOfLit cls;

fun clausesOfClauses clss = map clauseOfClause clss;

fun wclausesOfClauses clss = map (fn c => (c,RPx.zero_nata)) clss;

(* Replace strings with nats *)

fun addElem (m,max) x =
  (case Map.peekKey m x of
          SOME _ => (m,max) |
          NONE => (Map.insert m (x, (RPx.suc max)),RPx.suc max)
  )

fun mget (m,_) = Map.get m;

fun natTermOfStringTerm m (RPx.Var x) = 
      let val m' = addElem m x in (m', RPx.Var (mget m' x)) end
   |
    natTermOfStringTerm m (RPx.Fun (f, ts)) = 
      let val (m', ts') = natTermsOfStringTerms m ts 
          val m'' = addElem m' f
      in (m'', RPx.Fun (mget m'' f,ts')) end
and natTermsOfStringTerms m [] = (m,[]) |
    natTermsOfStringTerms m (t::ts) =
      (let val (m',ts') = natTermsOfStringTerms m ts
           val (m'',t') = natTermOfStringTerm m' t in
       (m'',t'::ts')
       end)

fun natLitOfStringLit m (RPx.Pos t) =
      (let val (m', t') = natTermOfStringTerm m t in
        (m', RPx.Pos t')
       end) |
    natLitOfStringLit m (RPx.Neg t) =
      (let val (m', t') = natTermOfStringTerm m t in
        (m', RPx.Neg t')
       end)

fun natClauseOfStringClause m [] = (m,[]) |
    natClauseOfStringClause m (l::ls) =
      (let val (m',ls') = natClauseOfStringClause m ls
           val (m'',l') = natLitOfStringLit m' l in
       (m'',l'::ls')
       end)

fun natClausesOfStringClauses' m [] = (m,[]) |
    natClausesOfStringClauses' m (c::cs) =
      (let val (m',cs') = natClausesOfStringClauses' m cs
           val (m'',c') = natClauseOfStringClause m' c in
       (m'',c'::cs')
       end)

val natClausesOfStringClauses = natClausesOfStringClauses' (Map.new StringOrdered.compare, RPx.zero_nata); 


fun string_of_term (RPx.Var x) = "X" ^ RPx.string_literal_of_nat x |
    string_of_term (RPx.Fun (f, ts)) = "f" ^ RPx.string_literal_of_nat f ^ " (" ^ string_of_terms ts
and string_of_terms [] = ")" |
    string_of_terms [l] = string_of_term l ^ ")" |
    string_of_terms (l::ls) = string_of_term l ^ ", " ^ string_of_terms ls; 

fun string_of_lit (RPx.Pos t) = "Pos (" ^ string_of_term t ^ ")" |
    string_of_lit (RPx.Neg t) = "Neg (" ^ string_of_term t ^ ")"

fun string_of_clause' [] = "]" |
    string_of_clause' [l] = string_of_lit l ^ "]" |
    string_of_clause' (l::ls) = string_of_lit l ^ ", " ^ string_of_clause' ls;

fun string_of_clause cs = "[" ^ string_of_clause' cs;

fun string_of_clauses' [] = "]" |
    string_of_clauses' [c] = string_of_clause c ^ "]" |
    string_of_clauses' (c::cs) = (string_of_clause c) ^ ", \n" ^ string_of_clauses' cs;
  
fun string_of_clauses cs = "[" ^ string_of_clauses' cs;

fun string_of_wclauses cs = string_of_clauses (map fst cs);

fun refute problem =
   (let
     val clauses = map LiteralSet.toList (Problem.toClauses problem)
     val RPclauses' = clausesOfClauses clauses
     val RPclauses = natClausesOfStringClauses RPclauses'
     val wclauses = wclausesOfClauses (#2 RPclauses)
     (*val _ = TextIO.print ("Clauses\n" ^ string_of_wclauses wclauses)*)
   in 
     RPx.prover wclauses
   end);

fun refuteAll limit filename tptp probs acc =
      case probs of
        [] =>
        (let
          val status =
              if !TEST then Tptp.UnknownStatus
              else if Tptp.hasFofConjecture tptp then Tptp.TheoremStatus
              else Tptp.UnsatisfiableStatus

          val () = display_status filename status

          val () =
              if !TEST then ()
              else display_proof filename tptp (List.rev acc)
        in
          true
        end)
      | prob :: probs =>
        (let
          val {subgoal,problem,sources} = prob

          val () = display_problem filename problem
        in
          if !TEST then refuteAll limit filename tptp probs acc
          else
            case refute problem of
              false =>
              (let
                val acc = acc
              in
                refuteAll limit filename tptp probs acc
              end)
            | true =>
              (let
                val status =
                    if Tptp.hasFofConjecture tptp then
                      Tptp.CounterSatisfiableStatus
                    else
                      Tptp.SatisfiableStatus

                val () = display_status filename status
              in
                false
              end)
        end) 
        handle SZS_Status_Inappropriate => 
          (let
             val status = Tptp.InappropriateStatus
             val () = display_status filename status
           in
             false
           end)

  fun prove limit mapping filename =
      (let
        val () = display_sep ()

        val () = display_name filename

        val tptp = read mapping filename

        val () = display_goal tptp

        val problems = Tptp.normalize tptp
      in
        refuteAll limit filename tptp problems []
      end);

fun proveAllRPx limit mapping filenames =
    List.all
      (if !QUIET then prove limit mapping
       else fn filename => prove limit mapping filename orelse true)
      filenames;

val proveAllRPxTest = proveAllRPx (newLimit ()) Tptp.defaultMapping

(* ------------------------------------------------------------------------- *)
(* Top level.                                                                *)
(* ------------------------------------------------------------------------- *)

fun toplevel _ =
(let
  val work = processOptions ()

  val () = if List.null work then usage "no input problem files" else ()

  val success = proveAllRPx (newLimit ()) Tptp.defaultMapping work
in
  exit {message = NONE, usage = false, success = success}
end)
