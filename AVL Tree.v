Require Export SfLib.

Inductive tree: Type :=
	| leaf : tree
	| node : nat -> nat -> tree -> tree -> tree.

Check node 5 2 (node 3 0 leaf leaf) leaf.

Definition left (t: tree) := 
	match t with
	| leaf => t
	| node _ _ leftChild _ => leftChild
	end.

Definition right (t: tree) := 
	match t with
	| leaf => t
	| node _ _ _ rightChild => rightChild
	end.


Fixpoint height (t: tree) :=
	match t with
	| leaf => 0
	| node _ _ leftChild rightChild => 1 + max (height leftChild) (height rightChild)
	end.

Definition insert (val:nat) (t: tree) := 
	node val (height t) leaf t.

Example leftexample :
	left (node 3 1 leaf (node 2 0 leaf leaf)) = leaf.
Proof. reflexivity. Qed.

Example rightexample :
	right (node 3 1 (node 2 0 leaf leaf) leaf) = leaf.
Proof. reflexivity. Qed.

Example insertexample :
	insert 5 leaf = node 5 0 leaf leaf.
Proof. reflexivity. Qed.
	
Example heightexample :
	height leaf = 0.
Proof. reflexivity. Qed.

Example heightexample2 :
	height (node 5 1 leaf (node 3 0 leaf leaf)) = 2.
Proof. reflexivity. Qed.

Fixpoint search (searchFor : nat) (t : tree) :=
	match t with
	| leaf => false
	| node val _ leftChild rightChild => match beq_nat val searchFor with
										| true => true
										| false => orb (search searchFor leftChild) (search searchFor rightChild)
										end
	end.

Example searchexample :
	search 5 (node 2 1 leaf (node 5 0 leaf leaf)) = true.
Proof. reflexivity. Qed.

Example searchexample2 : 
	search 5 leaf = false.
Proof. reflexivity. Qed.

Fixpoint wellformed (t: tree) :=
	match t with
	| leaf => true
	| node val weight leftChild rightChild => match beq_nat weight ((height leftChild) - (height rightChild)) with
												| false => false
												| true => andb (wellformed leftChild) (wellformed rightChild)
												end
	end.

Fixpoint inorder (t: tree) :=
	match t with
	| leaf => []
	| node val _ leftChild rightChild => (inorder leftChild)++val::(inorder rightChild)
	end.

Definition Tree :=
	 node 2 0 (node 1 0 leaf leaf) (node 5 0 leaf leaf).

Example inorder_test :
	inorder Tree = 1::2::5::[].
Proof. reflexivity. Qed.

Fixpoint is_sorted (l : list nat) :=
	match l with
	| x1::xs => match xs with
				| [] => true
				| x2::xss => andb (ble_nat x1 x2) (is_sorted xs)
				end
	| [] => true
	end.

Example is_sortedexample :
	is_sorted (inorder Tree) = true.
Proof. reflexivity. Qed.

Inductive sorted : list nat -> Prop :=
	empty : sorted []
	| single : forall n, sorted [n]
	| more : forall n m xs, ble_nat n m = true -> sorted (m::xs) -> sorted (n::m::xs).
	
Example propsorted :
	sorted (inorder Tree).
Proof. simpl. apply more. reflexivity. apply more. reflexivity. apply single. Qed.

Example propnonsorted :
	sorted (1::1::0::[]).
Proof. apply more. reflexivity. apply more. (*UNPOSSIBLE!!!*) Admitted.

Example hejmor : 
	sorted [5].
Proof.
	apply single.
Qed.