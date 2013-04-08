Require Export SfLib.

Inductive tree: Type :=
	| leaf : tree
	| node : nat -> nat -> tree -> tree -> tree.
	        (* Value -> Weight -> Left -> Right *)

Check node 5 2 (node 3 0 leaf leaf) leaf.

Definition left (t: tree) := 
	match t with
	| leaf => None
	| node _ _ leftChild _ => Some leftChild
	end.

Definition right (t: tree) := 
	match t with
	| leaf => None
	| node _ _ _ rightChild => Some rightChild
	end.


Fixpoint height (t: tree) :=
	match t with
	| leaf => 0
	| node _ _ leftChild rightChild => 1 + max (height leftChild) (height rightChild)
	end.


Fixpoint insert (val:nat) (t: tree) := 
	match t with
	| leaf => node val 0 leaf leaf
	| node treeval weight lChild rChild => match ble_nat val treeval with
										   | true => node treeval (weight+1) (insert val lChild) rChild
										   | false => node treeval (weight-1) lChild (insert val rChild)
										   end
	end.

Example insertexample:
	insert 2 (insert 5 leaf) = node 5 1 (node 2 0 leaf leaf) leaf.
Proof. reflexivity. Qed.

(*TODO: Look at weights *)
Fixpoint balance (t : tree) :=
	match t with
	| leaf => leaf
	| node val weight lChild rChild => 
		match weight+2 with
		| 0 => 
			match rChild with
			| leaf => leaf (* shouldn't happen *)
			| node rval rweight rlChild rrChild => 
				match rweight+2 with
				| 1 => node rval (height (node val weight lChild rlChild) - height rrChild) (node val weight lChild rlChild) rrChild (* rr *)
				| _ => 
					match rlChild with
						| leaf => leaf (* shouldn't happen*)
						| node rlval rlweight rllChild rlrChild => 
							node rlval 0 (node val weight lChild rllChild) (node rval 0 rlrChild rrChild) (* rl *)
					end
				end
			end
		| 4 => 
			match lChild with
			| leaf => leaf (* shouldn't happen *)
			| node lval lweight llChild lrChild => 
				match lweight+2 with
				| 1 => 
					match lrChild with
					| leaf => leaf (* shouldn't happen *)
					| node lrval lrweight lrlChild lrrChild => 
						node lrval 0 (node lval 0 llChild lrlChild) (node val 0 lrrChild rChild) (* lr *)
					end
				| _ => node lval 0 llChild (node val 0 lrChild rChild) (* ll *)
				end
			end
		| _ => node val weight (balance lChild) (balance rChild)
		end
	end.

Example leftexample :
	left (node 3 1 leaf (node 2 0 leaf leaf)) = Some leaf.
Proof. reflexivity. Qed.

Example rightexample :
	right (node 3 1 (node 2 0 leaf leaf) leaf) = Some leaf.
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
	| leaf => None
	| node val _ leftChild rightChild => match beq_nat val searchFor with
										| true => Some t
										| false => match ble_nat searchFor val with
												   | true => search searchFor leftChild
												   | false => search searchFor rightChild
												   end
										end
	end.

Example searchexample :
	search 5 (node 2 1 leaf (node 5 0 leaf leaf)) = Some (node 5 0 leaf leaf).
Proof. reflexivity. Qed.

Example searchexample2 : 
	search 5 leaf = None.
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