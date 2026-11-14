(* Le τ-reau, Model2: the concurrency rules of Kurt without the guard
   modifier, as a step relation.

   Primitives:
   - a context runs code: its k-th instruction is chosen from the
     registers of earlier ones (branches, loops); instruction k of a
     context that loads leaves its value in register k;
   - a context does its instructions in programme order; its next
     instruction is pcs. An access may also happen early, before the
     instructions in front of it. The model records it at a slot k > pcs
     (a guess of its place); when the context reaches slot k, the
     instruction there must be that same access, or the run goes no
     further. The guess is bookkeeping only: R1 below does not use it;
   - each cell keeps its own history of writes, extended by insertion,
     never shortened or reordered;
   - each context has a knowledge set P, an acquired-but-not-yet-taken set
     A, and a release set R; there is one shared set G that guard()
     publishes to and takes from.

   The three rules:
   R1 (independence)  a context does its instructions in programme order;
       an access may also happen before the instructions in front of it
       when, for every value the loads not yet done could return, the first
       of the context's coming instructions tied to it is that same access
       (same kind, cells and values); when the context reaches it, it
       does not happen again, and a read keeps the value it took. The tie
       table: same cell; either is guard(); acquire
       before anything, a load before acquire; release before a store,
       anything before release.
   Accesses may cover several cells (the parade): an indivisible access
   covers its cells as one. In this model every access instruction is
   indivisible; an access that is not (a plain multi-cell access, a CAS the
   transactionality set does not hold) is written cell by cell.
   R2 (history)       a read takes any write of its cell that is not older
       than a write the context knows; a write enters its cell's history
       after every write the context knows; a transaction's write enters
       immediately after the write it read, and nothing enters there later;
       a read with nothing tied to it since its context's previous access
       to the same cell may be bound to take that access's write; R1 may
       count on the value of a bound read, and the read then takes that
       write. Several cells: a write enters the histories of all its cells
       in one step, and the order of writes read in all histories together
       has no cycle; a read takes a write it may see in each of its cells
       and straddles no write (none is, or is older than, the write it
       takes in one cell and newer than the write it takes in another); a
       transaction enters right after the write it read in each cell.
   R3 (knowledge)     a write carries R; a read learns the write it read
       and puts what that write carries into A; acquire takes A; release
       sets R to P; guard() takes A and G and then publishes P to G. *)

From Stdlib Require Import Arith Lia List Bool Relations.
From Stdlib Require Arith.Cantor.
Import ListNotations.

Definition val := nat.
Definition cell := nat.
Definition regs := nat -> val.

(* the access mode: an access of the model has the one mode Plain, and is
   ordered only by its cells and by fences *)
Inductive mode : Set := Plain.
(* fences: guard() (tied to everything), and the four atoms. FLl relays loads
   (earlier loads before later loads), FSs relays stores, FLs withholds stores
   (earlier loads before later stores), FSl withholds loads (earlier stores
   before later loads). A fence with several atoms is its atoms as
   independent slots, untied to each other. *)
Inductive fk := FLl | FSs | FLs | FSl | FFull.

(* an access covers a list of cells; one cell is the list of one *)
Inductive instr :=
| ILd (m : mode) (xs : list cell) (c : regs -> bool)
| ISt (m : mode) (xs : list cell) (c : regs -> bool) (v : regs -> val)
| ICas (m : mode) (xs : list cell) (c : regs -> bool) (e n : regs -> val)
| IFn (f : fk)
| INop.

Definition prog := list (nat -> regs -> instr).
Definition code (p : prog) (c : nat) : nat -> regs -> instr := nth c p (fun _ _ => INop).
Definition ins (p : prog) (c k : nat) (r : regs) : instr := code p c k r.

(* the cells an access covers, each once *)
Definition dd (xs : list cell) : list cell := nodup Nat.eq_dec xs.

Definition icells (i : instr) : list cell :=
  match i with
  | ILd _ xs _ | ISt _ xs _ _ | ICas _ xs _ _ _ => dd xs
  | IFn _ | INop => []
  end.

Definition isacc (i : instr) : bool :=
  match i with ILd _ _ _ | ISt _ _ _ _ | ICas _ _ _ _ _ => true | _ => false end.

Definition is_load (i : instr) : bool :=
  match i with ILd _ _ _ | ICas _ _ _ _ _ => true | _ => false end.
Definition is_store (i : instr) : bool :=
  match i with ISt _ _ _ _ | ICas _ _ _ _ _ => true | _ => false end.

Definition is_cas (i : instr) : bool := match i with ICas _ _ _ _ _ => true | _ => false end.

(* the instruction tied to everything: guard() *)
Definition gop (i : instr) : bool :=
  match i with IFn FFull => true | _ => false end.

(* the fences *)
Definition isfence (i : instr) : bool := match i with IFn _ => true | _ => false end.

(* the same atom, as two fence instructions *)
Definition sameatom (a b : instr) : bool :=
  match a, b with
  | IFn FLl, IFn FLl | IFn FSs, IFn FSs | IFn FLs, IFn FLs | IFn FSl, IFn FSl => true
  | _, _ => false
  end.

(* the tie between an earlier instruction a and a later instruction b: a
   common cell; guard(); an access and an atom that
   orders it (a load before ll or ls, a store before ss or sl; ll or sl
   before a load, ss or ls before a store); two fences of the same atom *)
Definition tied (a b : instr) : Prop :=
  (exists x, In x (icells a) /\ In x (icells b))
  \/ gop a = true \/ gop b = true
  \/ (is_load a = true /\ (b = IFn FLl \/ b = IFn FLs))
  \/ (is_store a = true /\ (b = IFn FSs \/ b = IFn FSl))
  \/ ((a = IFn FLl \/ a = IFn FSl) /\ is_load b = true)
  \/ ((a = IFn FSs \/ a = IFn FLs) /\ is_store b = true)
  \/ sameatom a b = true.

(* the ties by role, so that proofs name the rule they use *)
Lemma tied_cell : forall a b x, In x (icells a) -> In x (icells b) -> tied a b.
Proof. intros a b x A B. left. exists x. auto. Qed.
Lemma tied_gop_l : forall a b, gop a = true -> tied a b.
Proof. intros a b G. right; left. exact G. Qed.
Lemma tied_gop_r : forall a b, gop b = true -> tied a b.
Proof. intros a b G. right; right; left. exact G. Qed.
Lemma tied_ld_l : forall a f, is_load a = true -> f = FLl \/ f = FLs -> tied a (IFn f).
Proof. intros a f A [-> | ->]; do 3 right; left; auto. Qed.
Lemma tied_st_s : forall a f, is_store a = true -> f = FSs \/ f = FSl -> tied a (IFn f).
Proof. intros a f A [-> | ->]; do 4 right; left; auto. Qed.
Lemma tied_l_ld : forall f b, f = FLl \/ f = FSl -> is_load b = true -> tied (IFn f) b.
Proof. intros f b [-> | ->] B; do 5 right; left; auto. Qed.
Lemma tied_s_st : forall f b, f = FSs \/ f = FLs -> is_store b = true -> tied (IFn f) b.
Proof. intros f b [-> | ->] B; do 6 right; left; auto. Qed.
Lemma tied_same : forall a b, sameatom a b = true -> tied a b.
Proof. intros a b S. do 7 right. exact S. Qed.

Definition ieval (i : instr) (r : regs) : bool * val * val :=
  match i with
  | ILd _ _ c => (c r, 0, 0)
  | ISt _ _ c v => (c r, v r, 0)
  | ICas _ _ c e n => (c r, e r, n r)
  | IFn _ | INop => (true, 0, 0)
  end.

Definition icond (i : instr) (r : regs) : bool := fst (fst (ieval i r)).

(* an instruction that comes: an access whose condition holds, or any other *)
Definition executes (i : instr) (r : regs) : bool :=
  if isacc i then icond i r else true.

(* the result of a CAS is a verdict (spec 0.1 §8.6): a success bit and the value
   read, in one register value *)
Definition vd (b : bool) (v : val) : val := Nat.b2n b + 2 * v.
Definition vok (a : val) : bool := Nat.odd a.
Definition vv (a : val) : val := Nat.div2 a.
Lemma vok_vd : forall b v, vok (vd b v) = b.
Proof.
  intros [] v; unfold vok, vd; simpl Nat.b2n.
  - rewrite Nat.add_1_l, Nat.odd_succ, Nat.even_mul. reflexivity.
  - rewrite Nat.add_0_l, <- Nat.negb_even, Nat.even_mul. reflexivity.
Qed.
Lemma vv_vd : forall b v, vv (vd b v) = v.
Proof.
  intros [] v; unfold vv, vd; simpl Nat.b2n.
  - rewrite Nat.add_1_l. apply Nat.div2_succ_double.
  - rewrite Nat.add_0_l. apply Nat.div2_double.
Qed.
Lemma vd_inj : forall b v b' v', vd b v = vd b' v' -> b = b' /\ v = v'.
Proof.
  intros b v b' v' E. split; [rewrite <- (vok_vd b v), <- (vok_vd b' v'), E|rewrite <- (vv_vd b v), <- (vv_vd b' v'), E]; reflexivity.
Qed.

Lemma vd_split : forall a, vd (vok a) (vv a) = a.
Proof. intros a. unfold vd, vok, vv. rewrite (Nat.div2_odd a) at 3. lia. Qed.

(* the register of an access that read v: a CAS's is its verdict *)
Definition areg (i : instr) (w : bool) (v : val) : val := match i with ICas _ _ _ _ _ => vd w v | _ => v end.
(* the value an access's register holds: a CAS's verdict holds a value *)
Definition rval (i : instr) (a : val) : val := match i with ICas _ _ _ _ _ => vv a | _ => a end.
Lemma rval_areg : forall i w v, rval i (areg i w v) = v.
Proof. intros i w v; destruct i; simpl; try reflexivity. apply vv_vd. Qed.
Lemma rval_iscas : forall i i' a, is_cas i = is_cas i' -> rval i a = rval i' a.
Proof. intros i i' a H. destruct i, i'; simpl in *; try discriminate; reflexivity. Qed.
Lemma rval_cas : forall i a, is_cas i = true -> rval i a = vv a.
Proof. intros i a H. destruct i; simpl in *; try discriminate; reflexivity. Qed.
Lemma areg_cas : forall i w v, is_cas i = true -> areg i w v = vd w v.
Proof. intros i w v H. destruct i; simpl in *; try discriminate; reflexivity. Qed.
Definition cexp (i : instr) (r : regs) : val := match i with ICas _ _ _ e _ => e r | _ => 0 end.
(* the free verdict bit of slot j under the free values f: f at a cell that is
   not one of the instruction's cells (f j x is consulted for a read only in
   its own cells) *)
Definition bitc (i : instr) : cell := S (list_max (icells i)).
Definition fbit (f : nat -> cell -> val) (i : instr) (j : nat) : bool := Nat.odd (f j (bitc i)).
Lemma odd_b2n : forall b, Nat.odd (Nat.b2n b) = b.
Proof. intros []; reflexivity. Qed.
Lemma bitc_notin : forall i x, In x (icells i) -> x <> bitc i.
Proof.
  intros i x H E. pose proof (proj1 (list_max_le (icells i) (list_max (icells i))) (le_n _)) as F.
  rewrite Forall_forall in F. specialize (F x H). unfold bitc in E. lia.
Qed.
Lemma cexp_ieval : forall i r r', ieval i r = ieval i r' -> cexp i r = cexp i r'.
Proof. intros i r r' H. destruct i; simpl in *; auto. injection H as _ E _. exact E. Qed.

(* a CAS at slot k whose condition holds and which fails, its register being
   v: v is a failure, or the value it holds differs from the expected value
   under the registers r *)
Definition cfailv (i : instr) (r : regs) (v : val) : bool :=
  match i with ICas _ _ c e _ => c r && (negb (vok v) || negb (Nat.eqb (vv v) (e r))) | _ => false end.
Definition cfail (i : instr) (r : regs) (k : nat) : bool := cfailv i r (r k).
Lemma cfailv_vd_true : forall i r a, is_cas i = true -> icond i r = true -> negb (cfailv i r (vd true a)) = Nat.eqb a (cexp i r).
Proof.
  intros i r a C Ic. destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in C; try discriminate.
  unfold icond, ieval in Ic; simpl in Ic. unfold cfailv. rewrite Ic, vok_vd, vv_vd. simpl. destruct (Nat.eqb a (e0 r)); reflexivity.
Qed.
Lemma cfailv_ok : forall i r r' v, is_cas i = true -> ieval i r = ieval i r' -> vok v = true ->
  vv v = (match i with ICas _ _ _ e _ => e r' | _ => 0 end) -> cfailv i r v = false.
Proof.
  intros i r r' v C E Vo Vv. destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in *; try discriminate.
  injection E as _ Ee _. rewrite Vo, Vv, Ee, Nat.eqb_refl. apply andb_false_r.
Qed.

(* the execution test, given whether slot k is the place of a CAS whose read
   half happened (h): an instruction executes unless its condition is false,
   or it is such a CAS and its comparison fails (its write
   half is nothing) *)
Definition xexec (h : bool) (i : instr) (r : regs) (k : nat) : bool :=
  executes i r && negb (h && cfail i r k).

(* ---------- values of several cells ---------- *)
(* a value of several cells is one value: enc packs the cells' values,
   projs unpacks them, exactly (Cantor pairing: a bijection between lists of
   a given length and values); for one cell both are the identity *)
Fixpoint enc (l : list val) : val :=
  match l with [] => 0 | [v] => v | v :: r => Cantor.to_nat (v, enc r) end.
Fixpoint projs (n : nat) (V : val) : list val :=
  match n with 0 => [] | S 0 => [V] | S n' => fst (Cantor.of_nat V) :: projs n' (snd (Cantor.of_nat V)) end.
Lemma projs_length : forall n V, length (projs n V) = n.
Proof. induction n as [|[|n] IH]; intros V; simpl; auto. f_equal. apply IH. Qed.

Lemma projs_enc : forall vs, vs <> [] -> projs (length vs) (enc vs) = vs.
Proof.
  induction vs as [|v [|w r] IH]; intros N; [congruence|reflexivity|].
  change (projs (S (length (w :: r))) (Cantor.to_nat (v, enc (w :: r))) = v :: w :: r).
  cbn [projs length]. rewrite Cantor.cancel_of_to. simpl. f_equal. apply IH. discriminate.
Qed.

Lemma enc_projs : forall n V, 1 <= n -> enc (projs n V) = V.
Proof.
  induction n as [|[|n] IH]; intros V L; [lia|reflexivity|].
  change (projs (S (S n)) V) with (fst (Cantor.of_nat V) :: projs (S n) (snd (Cantor.of_nat V))).
  destruct (Cantor.of_nat V) as [a b] eqn:E. cbn [fst snd].
  assert (Ne : projs (S n) b <> []) by (destruct n; simpl; discriminate).
  destruct (projs (S n) b) as [|y l] eqn:P; [congruence|].
  change (Cantor.to_nat (a, enc (y :: l)) = V). rewrite <- P, IH by lia.
  transitivity (Cantor.to_nat (Cantor.of_nat V)); [rewrite E; reflexivity|apply Cantor.cancel_to_of].
Qed.

(* the value of cell x among the cells xs with values vs *)
Fixpoint cval (xs : list cell) (vs : list val) (x : cell) : val :=
  match xs, vs with
  | y :: xs', v :: vs' => if Nat.eqb x y then v else cval xs' vs' x
  | _, _ => 0
  end.

(* ---------- what an access does: kind, mode, cells, values ---------- *)
Inductive desc :=
| DLd (m : mode) (xs : list cell)
| DSt (m : mode) (xs : list cell) (v : val)
| DCas (m : mode) (xs : list cell) (e n : val)
| DFn (f : fk).

Definition dof (i : instr) (r : regs) : option desc :=
  match i with
  | ILd m xs c => if c r then Some (DLd m xs) else None
  | ISt m xs c v => if c r then Some (DSt m xs (v r)) else None
  | ICas m xs c e n => if c r then Some (DCas m xs (e r) (n r)) else None
  | IFn _ | INop => None
  end.

Definition inst_of (d : desc) : instr :=
  match d with
  | DLd m xs => ILd m xs (fun _ => true)
  | DSt m xs v => ISt m xs (fun _ => true) (fun _ => v)
  | DCas m xs e n => ICas m xs (fun _ => true) (fun _ => e) (fun _ => n)
  | DFn f => IFn f
  end.

(* what an instruction does, for R1: an access's effect, or guard.rl() or
   guard.rs() (guard() is tied to every instruction and happens in order) *)
Definition eof (i : instr) (r : regs) : option desc :=
  match i with
  | IFn FFull => None
  | IFn f => Some (DFn f)
  | _ => dof i r
  end.

Lemma eof_cexp : forall i r d r', eof i r = Some d -> is_cas (inst_of d) = is_cas i /\ cexp (inst_of d) r' = cexp i r.
Proof.
  intros i r d r' H. destruct i as [m x c0|m x c0 v|m x c0 e n|f|]; simpl in H; try discriminate;
    [destruct (c0 r); [injection H as <-; split; reflexivity|discriminate]..|].
  destruct f; try discriminate; injection H as <-; split; reflexivity.
Qed.

(* ---------- knowledge sets ---------- *)
Definition view := nat -> Prop.
Definition vnil : view := fun _ => False.
Definition vor (a b : view) : view := fun w => a w \/ b w.
Definition vone (w : nat) : view := fun w' => w' = w.

(* ---------- cell histories ---------- *)
Definition hist := list (nat * bool).
Definition ids (h : hist) : list nat := map fst h.

Definition older (h : hist) (a b : nat) : Prop :=
  exists h1 h2, h = h1 ++ h2 /\ In a (ids h1) /\ In b (ids h2).

Definition free_head (h2 : hist) : Prop :=
  forall w g h', h2 = (w, g) :: h' -> g = false.

Definition visible (P : view) (h : hist) (u : option nat) : Prop :=
  match u with
  | None => forall w, P w -> ~ In w (ids h)
  | Some w => In w (ids h) /\ forall w', P w' -> ~ older h w w'
  end.

Definition enter (P : view) (h : hist) (t : nat) (h' : hist) : Prop :=
  exists h1 h2, h = h1 ++ h2 /\ (forall w, P w -> ~ In w (ids h2))
    /\ free_head h2 /\ h' = h1 ++ (t, false) :: h2.

Definition enter_tied (u : option nat) (h : hist) (t : nat) (h' : hist) : Prop :=
  exists h1 h2, h = h1 ++ h2
    /\ match u with None => h1 = [] | Some w => exists h0 g, h1 = h0 ++ [(w, g)] end
    /\ free_head h2 /\ h' = h1 ++ (t, true) :: h2.

(* several cells: a write enters each of its cells, the others are left alone *)
Definition enters (P : view) (H : cell -> hist) (xs : list cell) (t : nat) (H' : cell -> hist) : Prop :=
  forall x, (In x xs -> enter P (H x) t (H' x)) /\ (~ In x xs -> H' x = H x).
Definition enters_tied (u : cell -> option nat) (H : cell -> hist) (xs : list cell) (t : nat)
    (H' : cell -> hist) : Prop :=
  forall x, (In x xs -> enter_tied (u x) (H x) t (H' x)) /\ (~ In x xs -> H' x = H x).

(* the order of writes, read in all histories together, has no cycle *)
Definition hord (H : cell -> hist) (a b : nat) : Prop := exists x, older (H x) a b.
Definition hacyclic (H : cell -> hist) : Prop := forall a, ~ clos_trans nat (hord H) a a.

(* a read of several cells straddles no write: no write is, or is older
   than, the write it takes in one cell and newer than the write it takes in
   another *)
Definition at_or_past (h : hist) (u : option nat) (W : nat) : Prop :=
  u = Some W \/ exists w, u = Some w /\ older h W w.
Definition before (h : hist) (u : option nat) (W : nat) : Prop :=
  u = None \/ exists w, u = Some w /\ older h w W.
Definition nostraddle (H : cell -> hist) (xs : list cell) (u : cell -> option nat) : Prop :=
  forall W x1 x2, In x1 xs -> In x2 xs -> In W (ids (H x1)) -> In W (ids (H x2)) ->
    at_or_past (H x1) (u x1) W -> before (H x2) (u x2) W -> False.

Definition reads (P : view) (H : cell -> hist) (xs : list cell) (u : cell -> option nat) : Prop :=
  (forall x, In x xs -> visible P (H x) (u x)) /\ (forall x, ~ In x xs -> u x = None) /\
  (2 <= length xs -> nostraddle H xs u).

(* a read takes, in each of its cells, a write of the cell's history or the
   initial value; a write enters each of its cells' histories at some place.
   What it may take and where it enters is decided by evok. *)
Definition takes (H : cell -> hist) (xs : list cell) (u : cell -> option nat) : Prop :=
  (forall x, In x xs -> match u x with None => True | Some w => In w (ids (H x)) end) /\
  (forall x, ~ In x xs -> u x = None).
Definition places (H : cell -> hist) (xs : list cell) (t : nat) (H' : cell -> hist) : Prop :=
  forall x, (In x xs -> exists h1 h2, H x = h1 ++ h2 /\ H' x = h1 ++ (t, false) :: h2) /\
            (~ In x xs -> H' x = H x).

Definition upd {A} (f : nat -> A) (k : nat) (v : A) : nat -> A :=
  fun k' => if Nat.eqb k' k then v else f k'.

(* ---------- state ---------- *)
Record cst := mkC {
  oc : nat -> option nat;   (* when the access recorded at slot k happened *)
  rg : regs;                (* register k: the value it read *)
  ai : nat -> instr;        (* the instruction that acted at slot k *)
  rw : nat -> cell -> option nat;  (* in each cell, the write slot k read or made *)
  rv : nat -> cell -> val;         (* in each cell, the value slot k read *)
  bd : nat -> bool;         (* the reads R1 has counted on taking their binder's write *)
  vP : view; vA : view; vR : view;
  vO : view;                (* what the context knows in order *)
  vOg : view;               (* what it knows in order through guard() *)
  oh : nat -> option nat;   (* when the read of a CAS split at slot k happened *)
  fx : nat -> option bool   (* S3c: the result the CAS at place j has fixed (success or failure),
                               as its verdict bit; indexed by the place *) }.

(* the read half of the CAS at slot k happened *)
Definition ohb (cc : cst) (k : nat) : bool := match oh cc k with Some _ => true | None => false end.

(* the execution test at slot k of a context in state cc, under registers r *)
Definition xex (cc : cst) (i : instr) (r : regs) (k : nat) : bool := xexec (ohb cc k) i r k.

Record mst := mkM {
  mP : view; mA : view; mR : view; mG : view;
  mH : cell -> hist; mV : nat -> cell -> val; mC : nat -> view;
  mW : view                 (* the context's own writes *) }.

(* erf: per cell, the write the access read *)
Record oev := mkO { et : nat; ec : nat; ek : nat; eP : view; erf : cell -> option nat; ew : bool;
  eC : list cell;   (* the cells it accessed *)
  eR : list cell;   (* the cells it read *)
  eQ : view;        (* what it knew in order through guard(), and the writes it took in order *)
  eQc : view;       (* what it knew in order, guard.rl() included: within each cell *)
  eh : bool         (* the read of a CAS split in two *) }.

Record st := mkS {
  tm : nat;
  cs : nat -> cst;
  wv : nat -> cell -> val;
  wc : nat -> view;
  hs : cell -> hist;
  vG : view;
  pcs : nat -> nat;         (* the next instruction of each context *)
  tp : nat -> nat;          (* every slot recorded is below tp *)
  cm : list (nat * nat * nat); (* the order in which slots were passed, with the time *)
  lg : list oev;
  (* for proofs only: what R1 was checked against at each early access, by time *)
  es : nat -> option (cst * nat * nat * (nat -> bool)) }.

Definition nosrc : cell -> option nat := fun _ => None.

Definition cinit : cst :=
  mkC (fun _ => None) (fun _ => 0) (fun _ => INop) (fun _ _ => None) (fun _ _ => 0) (fun _ => false)
      vnil vnil vnil vnil vnil (fun _ => None) (fun _ => None).
Definition sinit : st :=
  mkS 0 (fun _ => cinit) (fun _ _ => 0) (fun _ => vnil) (fun _ => []) vnil
      (fun _ => 0) (fun _ => 0) [] [] (fun _ => None).

Definition gpre (m : mst) : mst :=
  let P := vor (vor (mP m) (mA m)) (mG m) in
  mkM P (mA m) P (mG m) (mH m) (mV m) (mC m) (mW m).
Definition gpost (m : mst) : mst :=
  let P := vor (mP m) (mA m) in mkM P (mA m) P P (mH m) (mV m) (mC m) (mW m).

Definition rdval (m : mst) (u : cell -> option nat) (x : cell) : val :=
  match u x with None => 0 | Some w => mV m w x end.
Definition rdvals (m : mst) (xs : list cell) (u : cell -> option nat) : list val := map (rdval m u) xs.
(* the writes a read took (an access reads none outside its cells) *)
Definition srcs (u : cell -> option nat) : view :=
  fun w => exists x, u x = Some w.
Definition carrieds (m : mst) (u : cell -> option nat) : view :=
  fun w' => exists x w, u x = Some w /\ (mC m w w' \/ w' = w).

Definition learn (m : mst) (u : cell -> option nat) : mst :=
  mkM (vor (mP m) (srcs u)) (vor (mA m) (carrieds m u)) (mR m) (mG m)
      (mH m) (mV m) (mC m) (mW m).

Definition wput (m : mst) (xs : list cell) (t : nat) (vs : list val) (H' : cell -> hist) : mst :=
  mkM (vor (mP m) (vone t)) (mA m) (mR m) (mG m) H'
      (upd (mV m) t (cval xs vs)) (upd (mC m) t (vor (mR m) (vone t))) (vor (mW m) (vone t)).

(* R2 and R3: what an instruction does to the state *)
Inductive eff (t : nat) : instr -> regs -> mst -> mst -> val -> view -> (cell -> option nat) -> bool -> Prop :=
| e_skip : forall i r m, isacc i = true -> icond i r = false ->
    eff t i r m m 0 (mP m) nosrc false
| e_ld : forall md xs c r m u,
    c r = true ->
    takes (mH m) (dd xs) u ->
    eff t (ILd md xs c) r m (learn m u) (enc (rdvals m (dd xs) u)) (mP m) u false
| e_st : forall md xs c v r m H',
    c r = true ->
    places (mH m) (dd xs) t H' ->
    eff t (ISt md xs c v) r m (wput m (dd xs) t (projs (length (dd xs)) (v r)) H') 0 (mP m) nosrc true
| e_cas_ok : forall md xs c e n r m u H',
    c r = true ->
    takes (mH m) (dd xs) u ->
    enc (rdvals m (dd xs) u) = e r ->
    places (mH m) (dd xs) t H' ->
    eff t (ICas md xs c e n) r m (wput (learn m u) (dd xs) t (projs (length (dd xs)) (n r)) H')
        (vd true (enc (rdvals m (dd xs) u))) (mP m) u true
| e_cas_no : forall md xs c e n r m u,
    c r = true ->
    takes (mH m) (dd xs) u ->
    eff t (ICas md xs c e n) r m (learn m u) (vd false (enc (rdvals m (dd xs) u))) (mP m) u false
| e_ll : forall r m,
    eff t (IFn FLl) r m (mkM (vor (mP m) (mA m)) (mA m) (mR m) (mG m) (mH m) (mV m) (mC m) (mW m))
        0 (mP m) nosrc false
| e_ss : forall r m,
    eff t (IFn FSs) r m (mkM (mP m) (mA m) (fun w => mR m w \/ (mP m w /\ mW m w)) (mG m) (mH m) (mV m) (mC m) (mW m))
        0 (mP m) nosrc false
| e_ls : forall r m,
    eff t (IFn FLs) r m (mkM (mP m) (mA m) (fun w => mR m w \/ ((mP m w \/ mA m w) /\ ~ mW m w)) (mG m) (mH m) (mV m) (mC m) (mW m))
        0 (mP m) nosrc false
| e_sl : forall r m,
    eff t (IFn FSl) r m (mkM (mP m) (mA m) (mR m) (vor (mG m) (mW m)) (mH m) (mV m) (mC m) (mW m))
        0 (mP m) nosrc false
| e_full : forall r m,
    eff t (IFn FFull) r m (gpost (gpre m)) 0 (mP (gpre m)) nosrc false
| e_nop : forall r m, eff t INop r m m 0 (mP m) nosrc false.

(* ---------- decidable tie ---------- *)
Definition fk_eqb (f g : fk) : bool :=
  match f, g with
  | FLl, FLl | FSs, FSs | FLs, FLs | FSl, FSl | FFull, FFull => true
  | _, _ => false
  end.
Definition isfn (f : fk) (i : instr) : bool :=
  match i with IFn g => fk_eqb g f | _ => false end.

Definition meetb (xs ys : list cell) : bool := existsb (fun x => existsb (Nat.eqb x) ys) xs.

Lemma meetb_spec : forall xs ys, meetb xs ys = true <-> exists x, In x xs /\ In x ys.
Proof.
  intros xs ys. unfold meetb. rewrite existsb_exists. split.
  - intros (x & I & E). apply existsb_exists in E. destruct E as (y & J & Q). apply Nat.eqb_eq in Q. subst. eauto.
  - intros (x & I & J). exists x. split; auto. apply existsb_exists. exists x. split; auto. apply Nat.eqb_refl.
Qed.

Definition tiedb (a b : instr) : bool :=
  meetb (icells a) (icells b)
  || gop a || gop b
  || (is_load a && (isfn FLl b || isfn FLs b)) || (is_store a && (isfn FSs b || isfn FSl b))
  || ((isfn FLl a || isfn FSl a) && is_load b) || ((isfn FSs a || isfn FLs a) && is_store b)
  || sameatom a b.

Lemma fk_eqb_eq : forall f g, fk_eqb f g = true <-> f = g.
Proof. intros [] []; simpl; split; intros H; try discriminate; try reflexivity; inversion H. Qed.

Lemma isfn_eq : forall f i, isfn f i = true <-> i = IFn f.
Proof.
  intros f [m x c|m x c v|m x c e n|g|]; simpl; split; intros H; try discriminate; try (inversion H; fail).
  - apply fk_eqb_eq in H. subst. reflexivity.
  - injection H as ->. apply fk_eqb_eq. reflexivity.
Qed.

Lemma tied_b : forall a b, tied a b -> tiedb a b = true.
Proof.
  intros a b H. unfold tiedb. repeat rewrite orb_true_iff. repeat rewrite andb_true_iff.
  repeat rewrite orb_true_iff. rewrite !isfn_eq.
  destruct H as [M|[H|[H|[H|[H|[H|[H|H]]]]]]]; [apply meetb_spec in M|..]; tauto.
Qed.

Lemma untied_b : forall a b, tiedb a b = false -> ~ tied a b.
Proof. intros a b H T. apply tied_b in T. congruence. Qed.

Lemma b_tied : forall a b, tiedb a b = true -> tied a b.
Proof.
  intros a b H. unfold tiedb in H. repeat rewrite orb_true_iff in H. repeat rewrite andb_true_iff in H.
  repeat rewrite orb_true_iff in H. rewrite !isfn_eq in H.
  destruct H as [[[[[[[H|H]|H]|H]|H]|H]|H]|H].
  - left. apply meetb_spec. auto.
  - right; left; auto.
  - right; right; left; auto.
  - do 3 right; left; auto.
  - do 4 right; left; auto.
  - do 5 right; left; auto.
  - do 6 right; left; auto.
  - do 7 right; auto.
Qed.

(* ---------- R1 ---------- *)

(* registers agree with every slot that is passed (before the next
   instruction pc) or has happened: those registers are fixed *)
Definition settled (cc : cst) (pc : nat) (r : regs) : Prop :=
  forall j, j < pc \/ oc cc j <> None -> r j = rg cc j.

(* the instruction is the same under every settled registers (true of every
   well-formed programme, see M2Inv.ord_determined) *)
Definition determined (p : prog) (cc : cst) (c k : nat) (i : instr) : Prop :=
  forall r, settled cc k r -> ins p c k r = i /\ ieval i r = ieval i (rg cc).

(* the accesses that happened early and are not yet reached *)
Definition pending (cc : cst) (pc k : nat) (d : desc) : Prop :=
  pc <= k /\ oc cc k <> None /\ ai cc k = inst_of d.

(* the record of a CAS's read at its slot: tied as the CAS *)
Definition crd (m : mode) (xs : list cell) : instr := ICas m xs (fun _ => true) (fun _ => 0) (fun _ => 0).

(* a CAS's read, ignoring the value operands: its mode and cells *)
Definition eofR (i : instr) (r : regs) : option (mode * list cell) :=
  match i with ICas m xs c _ _ => if c r then Some (m, xs) else None | _ => None end.

(* what R1 places: an access, or a CAS's read alone (its mode and cells) *)
Inductive tgt : Type := TF (d : desc) | TH (m : mode) (xs : list cell).
Coercion TF : desc >-> tgt.
Definition tinst (g : tgt) : instr := match g with TF d => inst_of d | TH m xs => crd m xs end.

(* the mode and cells of a CAS *)
Definition casx (i : instr) : option (mode * list cell) :=
  match i with ICas m xs _ _ _ => Some (m, xs) | _ => None end.

(* a CAS whose read happened alone and that is not yet reached *)
Definition hpending (cc : cst) (pc k : nat) (m : mode) (xs : list cell) : Prop :=
  pc <= k /\ oh cc k <> None /\ casx (ai cc k) = Some (m, xs).

(* the CAS at slot k whose read happened alone is the place of that read
   reached: of the pending accesses and reads alone tied to it, its read
   happened first (as s_match asks of an access reached) *)
Definition hfirst (cc : cst) (k : nat) (i : instr) : Prop :=
  forall t1, oh cc k = Some t1 ->
    (forall k' d' t', pending cc k k' d' -> k' <> k -> oc cc k' = Some t' -> tied i (inst_of d') -> t1 < t') /\
    (forall k' m xs t', hpending cc k k' m xs -> k' <> k -> oh cc k' = Some t' -> tied i (crd m xs) -> t1 < t').

(* its read happened alone and, at time T, its write has not happened yet *)
Definition hlive (cc : cst) (k T : nat) : Prop := forall t2, oc cc k = Some t2 -> T < t2.
Definition hliveb (cc : cst) (k T : nat) : bool := match oc cc k with Some t2 => Nat.ltb T t2 | None => true end.

(* under registers r, with the coming instructions Hc counted as happened and
   the coming instructions Hx taken (Hc and the places of CASes whose read
   happened alone; Hv j' v: j' is the place of a CAS whose read happened
   alone and read v), the first of the coming instructions (from pc) tied to g
   that is not counted as happened is at j, is g, and is not taken *)
Definition first_in (p : prog) (c pc : nat) (r : regs) (Hc Hx : nat -> Prop) (Hv : nat -> val -> Prop)
    (g : tgt) (j : nat) : Prop :=
  pc <= j /\ match g with TF d => eof (ins p c j r) r = Some d | TH m xs => eofR (ins p c j r) r = Some (m, xs) end /\
  ~ Hx j /\
  forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
    (forall v, Hv j' v -> cfailv (ins p c j' r) r v = false) ->
    tied (ins p c j' r) (tinst g) -> Hc j'.

(* the place of an access, or of a CAS's read alone, that happens at time T:
   the instructions that have happened are the places of the pending accesses
   that happened before T; the places of the CASes whose read happened alone
   before T are taken but have not happened (n bounds the nesting, n > T
   suffices) *)
Fixpoint plc (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (n T : nat) (g : tgt) (j : nat) : Prop :=
  match n with
  | 0 => False
  | S n' =>
      let Hc := fun j' => exists k' t' d', pending cc pc k' d' /\ oc cc k' = Some t' /\ t' < T /\
                   plc p c cc pc r n' t' (TF d') j' in
      let Hh := fun j' => exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\
                   hlive cc k' T /\ plc p c cc pc r n' t' (TH m' xs') j' in
      let Hv := fun j' v => exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\
                   hlive cc k' T /\ plc p c cc pc r n' t' (TH m' xs') j' /\ v = r j' in
      first_in p c pc r Hc (fun j' => Hc j' \/ Hh j') Hv g j
  end.

Definition first_at (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (T : nat) (d : desc) (j : nat) : Prop :=
  plc p c cc pc r (S T) T (TF d) j.

(* R1's place for a CAS's read alone happening at T *)
Definition first_atR (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (T : nat) (m : mode) (xs : list cell)
    (j : nat) : Prop :=
  plc p c cc pc r (S T) T (TH m xs) j.

(* the coming instruction j is the place of a pending access that happened
   before T *)
Definition taken (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (T j : nat) : Prop :=
  exists k t d, pending cc pc k d /\ oc cc k = Some t /\ t < T /\ first_at p c cc pc r t d j.

(* the coming instruction j is the place of a CAS whose read happened alone
   before T *)
Definition htaken (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (T j : nat) : Prop :=
  exists k t m xs, hpending cc pc k m xs /\ oh cc k = Some t /\ t < T /\ hlive cc k T /\ first_atR p c cc pc r t m xs j.

(* the same, with the value that read took *)
Definition htakenv (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (T j : nat) (v : val) : Prop :=
  exists k t m xs, hpending cc pc k m xs /\ oh cc k = Some t /\ t < T /\ hlive cc k T /\ first_atR p c cc pc r t m xs j /\
    v = r j.

(* ---------- decidable forms ---------- *)
Fixpoint lst_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Nat.eqb x y && lst_eqb a' b'
  | _, _ => false
  end.

Definition desc_eqb (d1 d2 : desc) : bool :=
  match d1, d2 with
  | DLd _ x1, DLd _ x2 => lst_eqb x1 x2
  | DSt _ x1 v1, DSt _ x2 v2 => lst_eqb x1 x2 && Nat.eqb v1 v2
  | DCas _ x1 e1 n1, DCas _ x2 e2 n2 => lst_eqb x1 x2 && Nat.eqb e1 e2 && Nat.eqb n1 n2
  | DFn f, DFn g => fk_eqb f g
  | _, _ => false
  end.

Definition odesc_eqb (o : option desc) (d : desc) : bool :=
  match o with Some d' => desc_eqb d' d | None => false end.

(* every j in [a, a + n) *)
Fixpoint allin (f : nat -> bool) (a n : nat) : bool :=
  match n with 0 => true | S n' => f a && allin f (S a) n' end.

Definition tatb (i : instr) (r : regs) (g : tgt) : bool :=
  match g with
  | TF d => odesc_eqb (eof i r) d
  | TH _ xs => match eofR i r with Some (_, xs') => lst_eqb xs' xs | None => false end
  end.

(* the decidable place; N bounds the slots recorded *)
Fixpoint fab (p : prog) (c : nat) (cc : cst) (pc N : nat) (r : regs) (n T : nat) (g : tgt) (j : nat) : bool :=
  match n with
  | 0 => false
  | S n' =>
      let tk := fun j' => existsb (fun k' => match oc cc k' with
                  | Some t' => Nat.ltb t' T && match eof (ai cc k') r with
                                              | Some d' => fab p c cc pc N r n' t' (TF d') j'
                                              | None => false end
                  | None => false end) (seq pc (N - pc)) in
      let th := fun j' => existsb (fun k' => match oh cc k' with
                  | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r n' t' (TH m' xs') j'
                                              | None => false end
                  | None => false end) (seq pc (N - pc)) in
      Nat.leb pc j && tatb (ins p c j r) r g && negb (tk j || th j) &&
      let thf := fun j' => existsb (fun k' => match oh cc k' with
                  | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r n' t' (TH m' xs') j' &&
                                                                  cfailv (ins p c j' r) r (r j')
                                              | None => false end
                  | None => false end) (seq pc (N - pc)) in
      allin (fun j' => tk j' || negb (tiedb (ins p c j' r) (tinst g) && executes (ins p c j' r) r && negb (thf j'))) pc (j - pc)
  end.

Definition first_atb (p : prog) (c : nat) (cc : cst) (pc N : nat) (r : regs) (T : nat) (d : desc) (j : nat) : bool :=
  fab p c cc pc N r (S T) T (TF d) j.

(* the one cell of a one-cell access *)
Definition one (xs : list cell) : option cell := match dd xs with [x] => Some x | _ => None end.

(* R2: the access a read at j may be counted on to take the write of, in its
   cell x: scanning back from j, the first instruction tied to the read; it
   must access x (a load, a store, a CAS, of one cell or several) *)
Fixpoint fbind (p : prog) (c : nat) (r : regs) (i : instr) (x : cell) (b : nat) : option nat :=
  match b with
  | 0 => None
  | S b' =>
      let a := ins p c b' r in
      if executes a r && tiedb a i then
        (if existsb (Nat.eqb x) (icells a) then Some b' else None)
      else fbind p c r i x b'
  end.

(* the reads R1 may count on: every load and the read of every CAS *)
Definition bread (i : instr) : bool :=
  match i with ILd _ _ _ | ICas _ _ _ _ _ => true | _ => false end.

Definition fbinder (p : prog) (c : nat) (r : regs) (j : nat) (x : cell) : option nat :=
  let i := ins p c j r in
  if bread i && icond i r && existsb (Nat.eqb x) (icells i) then fbind p c r i x j else None.

(* the pending access, if any, whose first coming tied instruction is at j;
   N bounds the slots recorded *)
Definition pend_at (p : prog) (c : nat) (cc : cst) (pc N : nat) (r : regs) (j : nat) : option nat :=
  find (fun k => match oc cc k with
                 | Some t => match eof (ai cc k) r with Some d => first_atb p c cc pc N r t d j | None => false end
                 | None => false
                 end) (seq pc (N - pc)).

(* ---------- a CAS's read alone ---------- *)

(* the CAS whose read happened alone, if any, whose place is j *)
Definition hpend_at (p : prog) (c : nat) (cc : cst) (pc N : nat) (r : regs) (j : nat) : option nat :=
  find (fun k => match oc cc k, oh cc k with
                 | None, Some t => match casx (ai cc k) with
                                   | Some (m, xs) => fab p c cc pc N r (S t) t (TH m xs) j
                                   | None => false end
                 | _, _ => false
                 end) (seq pc (N - pc)).

(* ---------- the ways the context may go on ---------- *)
(* Under the free values f of the loads not yet done (one per slot and cell),
   the value a read at j takes in cell x: as it is, before pc; for a read that
   comes, the value of the pending early read there if there is one, else the
   value R1 counts on it taking from its binder in x (B), else f j x. The
   value of a binder in x: what a load read there, what a store wrote there,
   what a CAS wrote there if it succeeded and read there if it failed. n
   bounds the nesting (n = j suffices: a binder comes before its read). *)
(* the value a binder at b gives a read of cell x: what a store wrote there,
   what a CAS wrote there if it succeeded; for a load, and a CAS that failed,
   what it read there (rd) *)
Definition bvx (p : prog) (c : nat) (r : regs) (b : nat) (x : cell) (rd : val) : val :=
  match ins p c b r with
  | ISt _ ys _ v => cval (dd ys) (projs (length (dd ys)) (v r)) x
  | ICas _ ys _ e nv => if vok (r b) then cval (dd ys) (projs (length (dd ys)) (nv r)) x else rd
  | _ => rd
  end.

Fixpoint cellv (p : prog) (c : nat) (cc : cst) (pc N : nat) (B : nat -> bool) (f : nat -> cell -> val)
    (r : regs) (n j : nat) (x : cell) : val :=
  if Nat.ltb j pc then rv cc j x else
  let i := ins p c j r in
  if is_load i && icond i r then
    match pend_at p c cc pc N r j with
    | Some k => rv cc k x
    | None =>
      match hpend_at p c cc pc N r j with
      | Some k => rv cc k x
      | None =>
        match n with
        | 0 => f j x
        | S n' =>
            if B j then
              match fbinder p c r j x with
              | Some b => bvx p c r b x (cellv p c cc pc N B f r n' b x)
              | None => f j x
              end
            else f j x
        end
      end
    end
  else 0.

(* S3c: the verdict of a CAS at place j whose result is fixed (fx): the fixed
   bit, success only where the comparison holds, with the value its read takes
   (a CAS that happened early as a whole gives its own verdict, which agrees:
   s_early, s_cwe) *)
Definition cfx (cc : cst) (j : nat) (i : instr) (r : regs) (a : val) : val :=
  if is_cas i then
    match fx cc j with
    | Some b => vd (b && Nat.eqb (vv a) (cexp i r)) (vv a)
    | None => a
    end
  else a.
Lemma cfx_unfold : forall cc j i r a, cfx cc j i r a =
  match fx cc j with Some b => if is_cas i then vd (b && Nat.eqb (vv a) (cexp i r)) (vv a) else a | None => a end.
Proof. intros. unfold cfx. destruct (is_cas i), (fx cc j); reflexivity. Qed.

(* register j: before pc as it is; a read that comes holds its cells' values *)
Definition slotv (p : prog) (c : nat) (cc : cst) (pc N : nat) (B : nat -> bool) (f : nat -> cell -> val)
    (r : regs) (j : nat) : val :=
  if Nat.ltb j pc then rg cc j else
  let i := ins p c j r in
  if is_load i && icond i r then
    match pend_at p c cc pc N r j with
    | Some k => rg cc k
    | None => cfx cc j i r
      (match hpend_at p c cc pc N r j with
      | Some k => if vok (rg cc k) then vd (negb (cfailv i r (rg cc k)) && fbit f i j) (vv (rg cc k)) else rg cc k
      | None => let v := enc (map (cellv p c cc pc N B f r j j) (icells i)) in
                if is_cas i then vd (Nat.eqb v (cexp i r) && fbit f i j) v else v
      end)
    end
  else 0.

Definition lreg (l : list val) : regs := fun i => nth i l 0.

Fixpoint bl (p : prog) (c : nat) (cc : cst) (pc N : nat) (B : nat -> bool) (f : nat -> cell -> val) (n : nat) : list val :=
  match n with
  | 0 => []
  | S n' => let l := bl p c cc pc N B f n' in l ++ [slotv p c cc pc N B f (lreg l) n']
  end.

Definition creg (p : prog) (c : nat) (cc : cst) (pc N : nat) (B : nat -> bool) (f : nat -> cell -> val) : regs :=
  fun j => nth j (bl p c cc pc N B f (S j)) 0.

Definition bor (B1 B2 : nat -> bool) : nat -> bool := fun j => B1 j || B2 j.

(* the slot whose record is the leader b's, if the leader has happened: b
   itself if passed; else the pending access whose place b is; else the CAS
   whose read happened alone and whose place b is (it gives what it read) *)
Definition lead (p : prog) (c : nat) (cc : cst) (pc N : nat) (r : regs) (b : nat) : option nat :=
  if Nat.ltb b pc then Some b else
  match pend_at p c cc pc N r b with Some k => Some k | None => hpend_at p c cc pc N r b end.

(* R1 for an early access d, which read u (if it reads), counting on the
   reads B, happening at time T: under every free values, the first coming
   instruction tied to d that has not happened (is not the place of a
   pending access) is d, and it is not the next instruction (an access that is next is not
   early); and a read whose place is a read R1 counts on takes the write of
   that read's binder, which has already happened *)
Definition early_ok (p : prog) (c : nat) (cc : cst) (pc N T : nat) (d : desc) (u : cell -> option nat)
    (B : nat -> bool) : Prop :=
  forall f, let r := creg p c cc pc N (bor (bd cc) B) f in
    exists j, pc < j /\ first_at p c cc pc r T d j /\
      (is_load (inst_of d) = true -> forall x b, In x (icells (inst_of d)) -> bor (bd cc) B j = true ->
         fbinder p c r j x = Some b -> exists k, lead p c cc pc N r b = Some k /\ u x = rw cc k x).

(* R1 for a CAS's read alone, at time T: under every free values, its place
   is a CAS of the same mode and cells; a read counted on there takes its
   binder's write *)
Definition early_okR (p : prog) (c : nat) (cc : cst) (pc N T : nat) (m : mode) (xs : list cell)
    (u : cell -> option nat) (B : nat -> bool) : Prop :=
  forall f, let r := creg p c cc pc N (bor (bd cc) B) f in
    exists j, first_atR p c cc pc r T m xs j /\
      (forall x b, In x (dd xs) -> bor (bd cc) B j = true -> fbinder p c r j x = Some b ->
         exists k, lead p c cc pc N r b = Some k /\ u x = rw cc k x).

(* R1 for the write of a CAS whose read happened alone at T1, at time T:
   under every free values, the place of the read is after the next
   instruction and is the CAS d, and every coming instruction before it tied
   to d has happened *)
Definition early_okW (p : prog) (c : nat) (cc : cst) (pc N T T1 : nat) (m : mode) (xs : list cell) (d : desc)
    (B : nat -> bool) : Prop :=
  forall f, let r := creg p c cc pc N (bor (bd cc) B) f in
    exists j, pc < j /\ first_atR p c cc pc r T1 m xs j /\ eof (ins p c j r) r = Some d /\
      forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
        (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
        tied (ins p c j' r) (inst_of d) -> taken p c cc pc r T j'.

(* S3c: once the value the read
   half of the CAS at place j takes is fixed (the same under every free
   values: the read half has been performed, or it is led, counting on the
   reads B), the CAS may fix its result, failure always, success only where
   the comparison holds. It has not happened as a whole; o is the record of
   its read half if that was performed (the same under every free values),
   whose result is not yet a failure. *)
Definition cfix_ok (p : prog) (c : nat) (cc : cst) (pc N j : nat) (b : bool) (B : nat -> bool)
    (o : option nat) : Prop :=
  exists v, forall f, let r := creg p c cc pc N (bor (bd cc) B) f in let i := ins p c j r in
    is_cas i = true /\ icond i r = true /\ pend_at p c cc pc N r j = None /\
    hpend_at p c cc pc N r j = o /\ (forall k, o = Some k -> vok (rg cc k) = true) /\
    vv (r j) = v /\ (b = true -> v = cexp i r).

(* a failure fixed after the read half: the record's register becomes a failure *)
Definition scfail (s : st) (c k : nat) : st :=
  let cc := cs s c in
  mkS (tm s)
      (upd (cs s) c (mkC (oc cc) (upd (rg cc) k (vd false (vv (rg cc k)))) (ai cc) (rw cc) (rv cc) (bd cc)
                         (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
      (wv s) (wc s) (hs s) (vG s)
      (pcs s) (tp s) (cm s) (lg s) (es s).
(* the result fixed at place j, the reads B counted on *)
Definition scfix0 (s : st) (c j : nat) (b : bool) (B : nat -> bool) : st :=
  let cc := cs s c in
  mkS (tm s)
      (upd (cs s) c (mkC (oc cc) (rg cc) (ai cc) (rw cc) (rv cc) (bor (bd cc) B)
                         (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (upd (fx cc) j (Some b))))
      (wv s) (wc s) (hs s) (vG s)
      (pcs s) (tp s) (cm s) (lg s) (es s).
Definition sflp (s : st) (c : nat) (o : option nat) (b : bool) : st :=
  match o with Some k => if b then s else scfail s c k | None => s end.

(* the register a passed slot k ends with agrees with the result fixed there *)
Definition fxok (cc : cst) (k : nat) (i : instr) (r : regs) (a : val) : Prop :=
  forall b, fx cc k = Some b -> is_cas i = true -> icond i r = true -> vok a = b && Nat.eqb (vv a) (cexp i r).

Definition mof (s : st) (c : nat) : mst :=
  let cc := cs s c in mkM (vP cc) (vA cc) (vR cc) (vG s) (hs s) (wv s) (wc s)
    (fun w => exists e, nth_error (lg s) w = Some e /\ ec e = c /\ ew e = true).

(* in each cell, the write an access read or made *)
Definition wrote (t : nat) (xs : list cell) (u : cell -> option nat) (w : bool) : cell -> option nat :=
  fun x => if w then (if existsb (Nat.eqb x) xs then Some t else None) else u x.

(* ---------- knowing in order ---------- *)
(* the context's own stores *)
Definition ownw (s : st) (c : nat) : view :=
  fun w => exists e, nth_error (lg s) w = Some e /\ ec e = c /\ ew e = true.
(* the view the context knows in order after instruction i *)
Definition newO (s : st) (c : nat) (i : instr) (m m' : mst) (O : view) : view :=
  match i with
  | IFn FFull => mP m'
  | IFn FLl => vor O (fun w => (mP m w \/ mA m w) /\ ~ (ownw s c w /\ ~ mG m w))
  | IFn FSl => vor O (mG m')
  | _ => O
  end.
(* the view the context knows in order through guard() after instruction i *)
Definition newOg (i : instr) (m' : mst) (Og : view) : view :=
  match i with IFn FFull => mP m' | IFn FSl => vor Og (mG m') | _ => Og end.
(* a write the access took is in order unless it is the context's own store not known in order *)
Definition tookord (s : st) (c : nat) (O : view) (u : cell -> option nat) : view :=
  fun k => (exists x, u x = Some k) /\ ~ (ownw s c k /\ ~ O k).
Definition evC (i : instr) (r : regs) : list cell := if isacc i && icond i r then icells i else [].
Definition evR (i : instr) (r : regs) : list cell := if is_load i && icond i r then icells i else [].
(* what an access knows in order through guard(), and what it took in order *)
Definition evQ (s : st) (c : nat) (i : instr) (r : regs) (m : mst) (Og O : view) (u : cell -> option nat)
    (w : bool) : view :=
  if w || (is_load i && icond i r) then vor Og (tookord s c O u) else vnil.
(* what a read knows in order, guard.rl() included (a write knows only
   what eQ says) *)
Definition evQc (i : instr) (r : regs) (O : view) (w : bool) : view :=
  if is_load i && icond i r then O else vnil.

(* ---------- one event: nothing comes before itself ---------- *)
(* the run's events are its log entries, named by their times *)
(* through: a write after the writes older than it in its histories; a read
   before the writes of its cells newer than the one it took; an access after
   what it knows in order (which includes the writes it took in order) *)
Definition gedge (s : st) (a b : nat) : Prop :=
  (exists x, older (hs s x) a b) \/
  (exists e x, nth_error (lg s) a = Some e /\ In x (eR e) /\ In b (ids (hs s x)) /\ b <> a /\
     match erf e x with None => True | Some u => older (hs s x) u b end) \/
  (exists e, nth_error (lg s) b = Some e /\ eQ e a /\ a <> b).
(* within one cell x the same, with the cell's part of each relation, and an
   access also after its context's earlier accesses to that cell *)
Definition cedge (s : st) (x : cell) (a b : nat) : Prop :=
  older (hs s x) a b \/
  (exists e, nth_error (lg s) a = Some e /\ In x (eR e) /\ In b (ids (hs s x)) /\ b <> a /\
     match erf e x with None => True | Some u => older (hs s x) u b end) \/
  (exists e, nth_error (lg s) b = Some e /\ In x (eR e) /\ erf e x = Some a /\ a <> b) \/
  (exists e, nth_error (lg s) b = Some e /\ In x (eC e) /\ (eQ e a \/ eQc e a) /\ In a (ids (hs s x)) /\ a <> b) \/
  (exists ea eb, nth_error (lg s) a = Some ea /\ nth_error (lg s) b = Some eb /\ ec ea = ec eb /\
     ek ea < ek eb /\ In x (eC ea) /\ In x (eC eb)).
Definition evok (s : st) : Prop :=
  (forall a, ~ clos_trans nat (gedge s) a a) /\ (forall x a, ~ clos_trans nat (cedge s x) a a).

Inductive step (p : prog) : st -> st -> Prop :=
(* the next instruction, in programme order *)
| s_ord : forall s c i m' a K u w,
    let cc := cs s c in
    let k := pcs s c in
    ins p c k (rg cc) = i ->
    executes i (rg cc) = true ->
    oc cc k = None ->
    oh cc k = None ->
    determined p cc c k i ->
    (executes i (rg cc) = true -> forall k' d, pending cc k k' d -> ~ tied i (inst_of d)) ->
    (executes i (rg cc) = true -> forall k' m xs, hpending cc k k' m xs -> ~ tied i (crd m xs)) ->
    (forall x b, bd cc k = true -> In x (icells i) -> fbinder p c (rg cc) k x = Some b -> u x = rw cc b x) ->
    eff (tm s) i (rg cc) (mof s c) m' a K u w ->
    (* a result fixed there (S3c) is the result *)
    fxok cc k i (rg cc) a ->
    step p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k i)
                              (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bd cc) (mP m') (mA m') (mR m')
                              (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s ++ [(c, k, tm s)])
           (lg s ++ [mkO (tm s) c k K u w (evC i (rg cc)) (evR i (rg cc)) (evQ s c i (rg cc) (mof s c) (vOg cc) (vO cc) u w) (evQc i (rg cc) (vO cc) w) false])
           (es s))
(* the next instruction, when it does not execute (an access whose condition
   is false, or a CAS whose read happened and whose comparison fails): the
   context passes it; it performs nothing, so nothing is logged and no time
   passes *)
| s_skip : forall s c i,
    let cc := cs s c in
    let k := pcs s c in
    ins p c k (rg cc) = i ->
    xex cc i (rg cc) k = false ->
    oc cc k = None ->
    (* a CAS whose read happened: the instruction reached is that CAS *)
    (oh cc k <> None -> eofR i (rg cc) = eofR (ai cc k) (rg cc)) ->
    (* it has committed to failure *)
    (oh cc k <> None -> vok (rg cc k) = false) ->
    hfirst cc k i ->
    determined p cc c k i ->
    fxok cc k i (rg cc) (rg cc k) ->
    step p s
      (mkS (tm s)
           (upd (cs s) c (mkC (oc cc) (rg cc) (upd (ai cc) k i) (rw cc) (rv cc) (bd cc)
                              (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
           (wv s) (wc s) (hs s) (vG s)
           (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s ++ [(c, k, tm s)]) (lg s) (es s))
(* an access early, recorded at slot k *)
| s_early : forall s c k d (B : nat -> bool) m' a K u w,
    let cc := cs s c in
    pcs s c < k ->
    oc cc k = None ->
    oh cc k = None ->
    (* a pending access that this one is tied to, as the earlier of the two,
       is recorded at an earlier slot *)
    (forall k' d', pending cc (pcs s c) k' d' -> tied (inst_of d) (inst_of d') -> k' < k) ->
    early_ok p c cc (pcs s c) (tp s c) (tm s) d u B ->
    eff (tm s) (inst_of d) (rg cc) (mof s c) m' a K u w ->
    (* a result fixed at its place (S3c) is its result *)
    (forall f j, first_at p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (tm s) d j ->
       fxok cc j (inst_of d) (rg cc) a) ->
    step p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k (inst_of d))
                              (upd (rw cc) k (wrote (tm s) (icells (inst_of d)) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bor (bd cc) B) (mP m') (mA m') (mR m')
                              (newO s c (inst_of d) (mof s c) m' (vO cc)) (newOg (inst_of d) m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s)
           (lg s ++ [mkO (tm s) c k K u w (evC (inst_of d) (rg cc)) (evR (inst_of d) (rg cc))
                         (evQ s c (inst_of d) (rg cc) (mof s c) (vOg cc) (vO cc) u w)
                         (evQc (inst_of d) (rg cc) (vO cc) w) false])
           (upd (es s) (tm s) (Some (cc, pcs s c, tp s c, B))))
(* the context reaches an access that happened early; from now on the slot
   records the programme's instruction, which does the same *)
| s_match : forall s c d,
    let cc := cs s c in
    let k := pcs s c in
    oc cc k <> None ->
    ai cc k = inst_of d ->
    eof (ins p c k (rg cc)) (rg cc) = Some d ->
    determined p cc c k (ins p c k (rg cc)) ->
    (* the access is the place reached: of the pending accesses tied to it,
       it happened first *)
    (forall k' d' t t', pending cc k k' d' -> k' <> k -> oc cc k = Some t -> oc cc k' = Some t' ->
       tied (inst_of d) (inst_of d') -> t < t') ->
    (forall k' m xs t t', hpending cc k k' m xs -> k' <> k -> oc cc k = Some t -> oh cc k' = Some t' ->
       tied (inst_of d) (crd m xs) -> t < t') ->
    fxok cc k (ins p c k (rg cc)) (rg cc) (rg cc k) ->
    step p s
      (mkS (tm s)
           (upd (cs s) c (mkC (oc cc) (rg cc) (upd (ai cc) k (ins p c k (rg cc))) (rw cc) (rv cc) (bd cc)
                              (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
           (wv s) (wc s) (hs s) (vG s)
           (upd (pcs s) c (S k)) (tp s) (cm s ++ [(c, k, tm s)]) (lg s) (es s))
(* a CAS's read alone, early or in order, recorded at slot k *)
| s_cread : forall s c k m xs (B : nat -> bool) m' a K u w (bv : bool),
    let cc := cs s c in
    let i := ILd m xs (fun _ => true) in
    pcs s c <= k ->
    oc cc k = None ->
    oh cc k = None ->
    (forall k' d', pending cc (pcs s c) k' d' -> tied (crd m xs) (inst_of d') -> k' < k) ->
    early_okR p c cc (pcs s c) (tp s c) (tm s) m xs u B ->
    eff (tm s) i (rg cc) (mof s c) m' a K u w ->
    (* the record carries the result fixed at its place (S3c), bv: a fixed
       failure, a fixed success only where the comparison holds, else a
       success; fixing a result does not suppress the read half *)
    (forall f j, first_atR p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (tm s) m xs j ->
       match fx cc j with Some b => b = bv | None => bv = true end /\
       fxok cc j (ins p c j (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f))
         (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (vd bv a)) ->
    step p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (oc cc) (upd (rg cc) k (vd bv a)) (upd (ai cc) k (crd m xs))
                              (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bor (bd cc) B) (mP m') (mA m') (mR m')
                              (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc))
                              (upd (oh cc) k (Some (tm s))) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s)
           (lg s ++ [mkO (tm s) c k K u w (evC i (rg cc)) (evR i (rg cc))
                         (evQ s c i (rg cc) (mof s c) (vOg cc) (vO cc) u w)
                         (evQc i (rg cc) (vO cc) w) true])
           (upd (es s) (tm s) (Some (cc, pcs s c, tp s c, B))))
(* the write of a CAS whose read happened alone, in order (it succeeds, with
   the writes the read took; a CAS that fails writes nothing and is passed by
   s_skip) *)
| s_cw : forall s c t1 i m' a K w,
    let cc := cs s c in
    let k := pcs s c in
    let u := rw cc k in
    ins p c k (rg cc) = i ->
    is_cas i = true ->
    oc cc k = None ->
    oh cc k = Some t1 ->
    (* the instruction reached is the CAS whose read happened *)
    eofR i (rg cc) = eofR (ai cc k) (rg cc) ->
    determined p cc c k i ->
    (forall k' d, pending cc k k' d -> ~ tied i (inst_of d)) ->
    (forall k' m xs, hpending cc k k' m xs -> k' <> k -> ~ tied i (crd m xs)) ->
    vok (rg cc k) = true ->
    eff (tm s) i (rg cc) (mof s c) m' a K u w ->
    w = true ->
    fxok cc k i (rg cc) a ->
    step p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k i)
                              (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bd cc) (mP m') (mA m') (mR m')
                              (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s ++ [(c, k, tm s)])
           (lg s ++ [mkO (tm s) c k K u w (evC i (rg cc)) (evR i (rg cc)) (evQ s c i (rg cc) (mof s c) (vOg cc) (vO cc) u w) (evQc i (rg cc) (vO cc) w) false])
           (es s))
(* the write of a CAS whose read happened alone, early (it succeeds) *)
| s_cwe : forall s c k t1 xs ev nv (B : nat -> bool) m' a K w,
    let cc := cs s c in
    let u := rw cc k in
    let d := DCas Plain xs ev nv in
    pcs s c < k ->
    oc cc k = None ->
    oh cc k = Some t1 ->
    ai cc k = crd Plain xs ->
    (forall k' d', pending cc (pcs s c) k' d' -> tied (inst_of d) (inst_of d') -> k' < k) ->
    early_okW p c cc (pcs s c) (tp s c) (tm s) t1 Plain xs d B ->
    vok (rg cc k) = true ->
    eff (tm s) (inst_of d) (rg cc) (mof s c) m' a K u w ->
    w = true ->
    (forall f j, first_atR p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) t1 Plain xs j ->
       fxok cc j (inst_of d) (rg cc) a) ->
    step p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k (inst_of d))
                              (upd (rw cc) k (wrote (tm s) (icells (inst_of d)) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bor (bd cc) B) (mP m') (mA m') (mR m')
                              (newO s c (inst_of d) (mof s c) m' (vO cc)) (newOg (inst_of d) m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s)
           (lg s ++ [mkO (tm s) c k K u w (evC (inst_of d) (rg cc)) (evR (inst_of d) (rg cc))
                         (evQ s c (inst_of d) (rg cc) (mof s c) (vOg cc) (vO cc) u w)
                         (evQc (inst_of d) (rg cc) (vO cc) w) false])
           (upd (es s) (tm s) (Some (cc, pcs s c, tp s c, B))))
(* S3c (one rule, one step): the CAS at place j
   fixes its result b (cfix_ok); when its read half was performed (record o),
   a failure makes the record's register a failure (spurious failure, spec 0.1
   §8.6), and from then on its write half is nothing; nothing is performed,
   logged or timed. The result is the result when the CAS is reached (fxok). *)
| s_cfix : forall s c j b (B : nat -> bool) o,
    let cc := cs s c in
    pcs s c <= j ->
    fx cc j = None ->
    cfix_ok p c cc (pcs s c) (tp s c) j b B o ->
    step p s (scfix0 (sflp s c o b) c j b B).

Inductive run (p : prog) : st -> Prop :=
| r0 : run p sinit
| rS : forall s s', run p s -> step p s s' -> run p s'.

Definition fin (p : prog) (n : nat -> nat) : Prop := forall c k r, n c <= k -> ins p c k r = INop.
(* every context has passed its last instruction, and nothing it did early
   is left unreached *)
Definition complete (p : prog) (n : nat -> nat) (s : st) : Prop :=
  forall c, c < length p -> n c <= pcs s c /\ forall k, pcs s c <= k -> oc (cs s c) k = None /\ oh (cs s c) k = None.
Definition done (p : prog) (s : st) : Prop := exists n, fin p n /\ complete p n s.

Definition final (s : st) (x : cell) : val :=
  match rev (hs s x) with [] => 0 | (w, _) :: _ => wv s w x end.

(* ---------- sequential executions (interleavings) ---------- *)
Record sst := mkSS { sp : nat -> nat; sr : nat -> regs; sm : cell -> val }.
(* sacc: cells, whether it writes; sg: guard() *)
Record sev := mkE { sx : nat; sk : nat; sacc : option (list cell * bool); sg : bool }.

Definition ssinit : sst := mkSS (fun _ => 0) (fun _ _ => 0) (fun _ => 0).

(* the memory with the cells xs set to the values vs *)
Definition mupd (m : cell -> val) (xs : list cell) (vs : list val) : cell -> val :=
  fun y => if existsb (Nat.eqb y) xs then cval xs vs y else m y.

Inductive sstep (p : prog) : sst -> sev -> sst -> Prop :=
| ss_skip : forall s c i, ins p c (sp s c) (sr s c) = i -> isacc i = true ->
    icond i (sr s c) = false ->
    sstep p s (mkE c (sp s c) None false)
      (mkSS (upd (sp s) c (S (sp s c))) (sr s) (sm s))
| ss_ld : forall s c md xs cnd, ins p c (sp s c) (sr s c) = ILd md xs cnd ->
    cnd (sr s c) = true ->
    sstep p s (mkE c (sp s c) (Some (dd xs, false)) false)
      (mkSS (upd (sp s) c (S (sp s c)))
            (upd (sr s) c (upd (sr s c) (sp s c) (enc (map (sm s) (dd xs))))) (sm s))
| ss_st : forall s c md xs cnd v, ins p c (sp s c) (sr s c) = ISt md xs cnd v ->
    cnd (sr s c) = true ->
    sstep p s (mkE c (sp s c) (Some (dd xs, true)) false)
      (mkSS (upd (sp s) c (S (sp s c))) (sr s)
            (mupd (sm s) (dd xs) (projs (length (dd xs)) (v (sr s c)))))
| ss_cas : forall s c md xs cnd e n (b : bool), ins p c (sp s c) (sr s c) = ICas md xs cnd e n ->
    cnd (sr s c) = true ->
    let ok := Nat.eqb (enc (map (sm s) (dd xs))) (e (sr s c)) && b in
    sstep p s (mkE c (sp s c) (Some (dd xs, ok)) false)
      (mkSS (upd (sp s) c (S (sp s c)))
            (upd (sr s) c (upd (sr s c) (sp s c) (vd ok (enc (map (sm s) (dd xs))))))
            (if ok then mupd (sm s) (dd xs) (projs (length (dd xs)) (n (sr s c))) else sm s))
| ss_fn : forall s c f, ins p c (sp s c) (sr s c) = IFn f ->
    sstep p s (mkE c (sp s c) None (match f with FFull => true | _ => false end))
      (mkSS (upd (sp s) c (S (sp s c))) (sr s) (sm s))
| ss_nop : forall s c, ins p c (sp s c) (sr s c) = INop ->
    sstep p s (mkE c (sp s c) None false)
      (mkSS (upd (sp s) c (S (sp s c))) (sr s) (sm s)).

Inductive srun (p : prog) : list sev -> sst -> Prop :=
| sr0 : srun p [] ssinit
| srS : forall l s e s', srun p l s -> sstep p s e s' -> srun p (l ++ [e]) s'.

Definition gsync (l : list sev) (i j : nat) (ci cj : nat) : Prop :=
  exists i' j' f1 f2, i <= i' /\ i' <= j' /\ j' <= j /\
    nth_error l i' = Some f1 /\ nth_error l j' = Some f2 /\
    sg f1 = true /\ sg f2 = true /\ sx f1 = ci /\ sx f2 = cj.

(* instruction k of context c is a fenced access slot *)
Definition fa (p : prog) (c k : nat) : Prop :=
  1 <= k /\ forall r, ins p c (k - 1) r = IFn FFull /\ ins p c (S k) r = IFn FFull.

(* a race: a conflicting pair of accesses of two contexts (a common cell, one
   writes), not both fenced, that no pair of guard() orders *)
Definition racy_g (p : prog) (l : list sev) : Prop :=
  exists i j e1 e2 x xs1 xs2 w1 w2,
    i < j /\ nth_error l i = Some e1 /\ nth_error l j = Some e2 /\
    sx e1 <> sx e2 /\
    sacc e1 = Some (xs1, w1) /\ sacc e2 = Some (xs2, w2) /\ In x xs1 /\ In x xs2 /\
    orb w1 w2 = true /\ ~ (fa p (sx e1) (sk e1) /\ fa p (sx e2) (sk e2)) /\
    ~ gsync l i j (sx e1) (sx e2).

Definition race_free_g (p : prog) : Prop := forall l s, srun p l s -> ~ racy_g p l.

Definition wf (p : prog) : Prop :=
  forall c k r r', (forall j, j < k -> r j = r' j) ->
    ins p c k r = ins p c k r' /\ ieval (ins p c k r) r = ieval (ins p c k r) r'.
