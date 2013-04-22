Require Export SfLib.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Inductive tree: Type :=
	| leaf : tree
	| node : nat -> tree -> tree -> tree.
	        (* Value -> Left -> Right *)

Definition left (t: tree) := 
	match t with
	| leaf => None
	| node _ leftChild _ => Some leftChild
	end.

Definition right (t: tree) := 
	match t with
	| leaf => None
	| node _ _ rightChild => Some rightChild
	end.


Fixpoint height (t: tree) :=
	match t with
	| leaf => 0
	| node _ leftChild rightChild => 1 + max (height leftChild) (height rightChild)
	end.

Fixpoint add (val:nat) (t: tree) := 
	match t with
	| leaf => node val leaf leaf
	| node treeval lChild rChild => 
		match ble_nat val treeval with
		| true => node treeval (add val lChild) rChild
		| false => node treeval lChild (add val rChild)
		end
	end.

Example addexample:
	add 2 (add 5 leaf) = node 5 (node 2 leaf leaf) leaf.
Proof. reflexivity. Qed.

(*TODO: Look at weights *)
Fixpoint balance (t : tree) :=
	match t with
	| leaf => leaf
	| node val lChild rChild => 
		match (height lChild) + 2 - (height rChild) with
		| 0 => 
			match rChild with
			| leaf => leaf (* shouldn't happen *)
			| node rval rlChild rrChild => 
				match (height rlChild) + 2 - (height rrChild) with
				| 1 => node rval (node val lChild rlChild) rrChild (* rr *)
				| _ => 
					match rlChild with
					| leaf => leaf (* shouldn't happen*)
					| node rlval rllChild rlrChild => 
						node rlval (node val lChild rllChild) (node rval rlrChild rrChild) (* rl *)
					end
				end
			end
		| 4 => 
			match lChild with
			| leaf => leaf (* shouldn't happen *)
			| node lval llChild lrChild => 
				match (height llChild) + 2 - (height lrChild) with
				| 1 => 
					match lrChild with
					| leaf => leaf (* shouldn't happen *)
					| node lrval lrlChild lrrChild => 
						node lrval (node lval llChild lrlChild) (node val lrrChild rChild) (* lr *)
					end
				| _ => node lval llChild (node val lrChild rChild) (* ll *)
				end
			end
		| _ => node val (balance lChild) (balance rChild)
		end
	end.

Definition insert val t :=
	balance (add val t).

Example leftexample :
	left (node 3 leaf (node 2 leaf leaf)) = Some leaf.
Proof. reflexivity. Qed.

Example rightexample :
	right (node 3 (node 2 leaf leaf) leaf) = Some leaf.
Proof. reflexivity. Qed.

Example add_example :
	add 5 leaf = node 5 leaf leaf.
Proof. reflexivity. Qed.
	
Example heightexample :
	height leaf = 0.
Proof. reflexivity. Qed.

Example heightexample2 :
	height (node 5 leaf (node 3 leaf leaf)) = 2.
Proof. reflexivity. Qed.

Fixpoint search (searchFor : nat) (t : tree) :=
	match t with
	| leaf => None
	| node val leftChild rightChild => 
		match beq_nat val searchFor with
		| true => Some t
		| false => 
			match ble_nat searchFor val with
			| true => search searchFor leftChild
			| false => search searchFor rightChild
			end
		end
	end.

Example searchexample :
	search 5 (node 2 leaf (node 5 leaf leaf)) = Some (node 5 leaf leaf).
Proof. reflexivity. Qed.

Example searchexample2 : 
	search 5 leaf = None.
Proof. reflexivity. Qed.

Fixpoint inorder (t: tree) :=
	match t with
	| leaf => []
	| node val leftChild rightChild => (inorder leftChild)++val::(inorder rightChild)
	end.

Definition Tree :=
	 node 2 (node 1 leaf leaf) (node 5 leaf leaf).

Example inorder_test :
	inorder Tree = 1::2::5::[].
Proof. reflexivity. Qed.

Inductive sorted : list nat -> Prop :=
	| empty : sorted []
	| single : forall n, sorted [n]
	| more : forall n m xs, ble_nat n m = true -> sorted (m::xs) -> sorted (n::m::xs).
	
Example propsorted :
	sorted (inorder Tree).
Proof. simpl. repeat apply more; try reflexivity. apply single. Qed.

Example propnonsorted :
	sorted (1::1::0::[]).
Proof. apply more. reflexivity. apply more. (*UNPOSSIBLE!!!*) Admitted.

Example balanced_tree :
	insert 5 (insert 2 (insert 10 (insert 1 leaf))) = node 2 (node 1 leaf leaf) (node 10 (node 5 leaf leaf) leaf).
Proof. reflexivity. Qed.

Lemma empty_app : forall (l1: list nat) (l2 : list nat),
	 [] = l1 ++ l2 -> l1 = [] /\ l2 = [].
Proof.
	intros. admit.
Qed.

Lemma cons_sorted : forall n l,
	sorted (n::l) -> sorted l.
Proof. 
	intros. inversion H. 
		apply empty. 
		subst. apply H3.
Qed.

Lemma concat_app_sorted : forall n l1 l2,
	sorted (n :: l1 ++ l2) -> sorted (n::l1).
Proof.
	intros. inversion H. 
		subst. apply empty_app in H2. inversion H2. rewrite H0. apply single. 
		subst. destruct l1.
			apply single.
			inversion H. subst.
			apply more. apply H5. simpl in *.  
Qed.

Lemma concat_app_sorted' : forall n l1 l2,
	sorted (l1 ++ n::l2) -> sorted (n::l2).
Proof.
	intros. admit.
Qed.

Lemma sorted_app: forall l1 l2,
	sorted(l1++l2) -> sorted l1 /\ sorted l2.
Proof. 
	intros. split.  
		destruct l1. 
			apply empty.
			simpl in H. apply concat_app_sorted in H. apply H.
		destruct l2.
			apply empty.
			apply concat_app_sorted' in H. apply H. 
Qed.

Fixpoint contains elem l :=
	match l with
	| [] => false
	| x::xs =>
		match beq_nat elem x with
		| true => true
		| false => contains elem xs
		end
	end.

Lemma app_sorted : forall l1 l2 e1 e2 xs1 xs2,
	l1 = xs1 ++ [e1] -> l2 = e2::xs2 -> sorted l1 -> sorted l2 -> ble_nat e1 e2 = true -> sorted(l1++l2).
Proof. Admitted.

Lemma add_insures_contains : forall elem t,
	 contains elem (inorder (add elem t)) = true.
Proof. 
	intros. induction t. 
		simpl. rewrite <- beq_nat_refl. reflexivity. 
		simpl. remember (ble_nat elem n) as guard. destruct guard.
			simpl. admit. admit.
Qed.

Theorem cons_app : forall e (l: list nat),
	[e]++l = e::l.
Proof.
	intros. simpl. reflexivity.
Qed.

Definition blt_nat n1 n2 :=
	negb (ble_nat n2 n1).

Definition bgt_nat n1 n2 :=
	negb (ble_nat n1 n2).

Lemma inorder_add : forall n t t' x' xs',
	inorder t' = x'::xs' -> t' = add n t -> inorder (add n t) = x'::xs'.
Proof.
	intros. subst. apply H.
Qed.

Fixpoint valid_bst t :=
	match t with
	| leaf => true
	| node val lChild rChild => 
		match lChild with
		| leaf => match rChild with
			| leaf => true
			| node rVal rlChild rrChild => andb (andb (bgt_nat rVal val) (valid_bst rlChild)) (valid_bst rrChild)
			end
		| node lVal llChild lrChild => match rChild with
			| leaf => andb (andb (ble_nat lVal val) (valid_bst llChild)) (valid_bst lrChild)
			| node rVal rlChild rrChild => 
				andb (andb (andb (ble_nat lVal val) (bgt_nat rVal val))  
				(andb (valid_bst llChild) (valid_bst lrChild)))
				(andb (valid_bst rlChild) (valid_bst rrChild))
			end
		end
	end.

Inductive bst : tree -> Prop :=
	| bst_leaf : bst leaf
	| bst_node : forall val rVal lVal llT lrT rlT rrT, 
		ble_nat lVal val = true -> bgt_nat rVal val = true -> bst (node lVal llT lrT) -> 
		bst (node rVal lrT rrT) -> bst (node val (node lVal llT lrT) (node rVal rlT rrT))
	| bst_node_leaf : forall val lVal llT lrT, 
		ble_nat lVal val = true -> bst (node lVal llT lrT) -> 
		bst (node val (node lVal llT lrT) leaf)
	| bst_leaf_node : forall val rVal rlT rrT, 
		bgt_nat rVal val = true -> bst (node rVal rlT rrT) -> 
		bst (node val leaf (node rVal rlT rrT))
	| bst_leaf_leaf : forall val, bst (node val leaf leaf).

Definition BigTree :=
	 node 6 (Tree) (node 10 leaf leaf).

Definition not_bst :=
	node 5 (node 6 leaf leaf) leaf.

Example big_tree_prop_example :
	bst BigTree.
Proof. unfold BigTree. apply bst_node; try repeat reflexivity; try repeat constructor. Qed.

Example not_bst_prop_example:
	bst not_bst.
Proof. unfold not_bst. apply bst_node_leaf. Admitted. (*UNPOSSIBLE*)

Example big_tree_example :
	valid_bst BigTree = true.
Proof. reflexivity. Qed.

Example not_bst_example :
	valid_bst not_bst = false.
Proof. reflexivity. Qed.

Definition BigTree2 :=
	node 5 leaf BigTree.
	
Example big_tree_2_example:
	valid_bst BigTree2 = true.
Proof. reflexivity. Qed.

Lemma add_preserves_bst : forall n t,
	bst t -> bst (add n t).
Proof.
	intros. induction t.
		constructor.
		simpl. remember (ble_nat n n0) as b. destruct b.
			admit. admit.
Qed.


(*
Theorem add_preserves_bst: forall n t,
	sorted (inorder t) -> sorted (inorder (add n t)).
Proof.
	intros. induction t. 
		Case "leaf". apply single.
		Case "node". simpl in H. apply sorted_app in H. inversion H. simpl. 
			remember (ble_nat n n0) as add. destruct add. 
				simpl. rewrite inorder_add with (t':=add n t1)(x':=batman)(xs':=alfred). remember (add n t1) as addnt1. destruct addnt1. 
					inversion Heqaddnt1. rewrite inorder_add with (n:=n)(t:=t1)(t':=add n t1). apply app_sorted.
					apply add_insures_contains. reflexivity. apply IHt1. apply H0. apply H1. symmetry. apply Heqadd. 
				simpl. apply app_sorted2 with (e1:=n0)(e2:=n)(xs2:=inorder (add n t2)). 
					simpl. remember (beq_nat n n0) as beqnat. destruct beqnat. 
						reflexivity. 
						apply add_insures_contains. reflexivity. apply H0. rewrite <- cons_app. apply spec_split_inorder_add_sort.
							apply single. apply IHt2. rewrite <- cons_app in H1. apply sorted_app in H1. inversion H1. apply H3.
							unfold blt_nat. rewrite <- Heqadd. reflexivity. 
Qed.
*)

Theorem insert_preserves_balance: forall n t t',
	t = insert n t' -> ble_nat (height t) (log2 (length (inorder t') + 1)+1) = true.
Proof. 
	intros. induction t'.
		Case "leaf". rewrite H. reflexivity.
		Case "node". simpl in *. rewrite H. destruct t'1. destruct t'2. simpl. admit. simpl.

Qed.		

Example justasmalltowngirl :
	2+2=4.
Proof. reflexivity. Qed.