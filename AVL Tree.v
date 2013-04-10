Require Export SfLib.

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

Lemma sorted_app: forall l1 l2,
	sorted(l1++l2) -> sorted l1 /\ sorted l2.
Proof. 
	intros. split. 
		destruct l1. 
			apply empty.
			simpl in H. admit.
		admit.
Qed.

Theorem insert_preserves_bst: forall n t,
	sorted (inorder t) -> sorted (inorder (add n t)).
Proof.
	intros. induction t. 
		Case "leaf". apply single.
		Case "node". simpl in H. apply sorted_app in H. admit.
Qed.

Fixpoint pow base exponent :=
	match exponent with
	| 0 => 1
	| S n => base * (pow base (n))
	end.

Example powcheck :
	pow 5 2 = 25.
Proof. reflexivity. Qed.

Fixpoint log n c :=
	match andb (ble_nat (pow 2 c) n) (negb (beq_nat (pow 2 c) n)) with
	| false => c
	| true => log n (c+1)
	end.
	
Example log :
	5*3 = 15.
Proof. compute. reflexivity. Qed.

Theorem insert_preserves_balance: forall n t t',
	t = insert n t' -> height t = log2 (length (inorder t')+1).
Proof. 
	intros. induction t'.
		Case "leaf". rewrite H. simpl. compute. reflexivity.
		Case "node". rewrite H. simpl. destruct t'1. destruct t'2. simpl. compute.
		
Example justasmalltowngirl :
	2+2=4.
Proof. reflexivity. Qed.