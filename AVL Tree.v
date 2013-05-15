Require Export SfLib.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition blt_nat n1 n2 :=
	negb (ble_nat n2 n1).

Definition bgt_nat n1 n2 :=
	negb (ble_nat n1 n2).

Fixpoint contains elem l :=
	match l with
	| [] => false
	| x::xs =>
		match beq_nat elem x with
		| true => true
		| false => contains elem xs
		end
	end.

Fixpoint first l :=
	match l with
	| nil => 0
	| x::xs => x
	end.

Fixpoint last l :=
	match l with
	| nil => 0
	| [x] => x
	| _::xs => last xs
	end.

Inductive tree: Type :=
	| leaf : tree
	| node : nat -> tree -> tree -> tree.
	        (* Value -> Left -> Right *)

Inductive sorted : list nat -> Prop :=
	| empty : sorted []
	| single : forall n, sorted [n]
	| more : forall n m xs, n <= m -> sorted (m::xs) -> sorted (n::m::xs).

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

Fixpoint balance (t : tree) :=
	match t with
	| leaf => leaf (*Leaf tree is already balanced*)
	| node val lChild rChild => 
		match (height lChild) + 2 - (height rChild) with
		| 0 => (*-2, unbalanced to the right*)
			match rChild with
			| leaf => leaf (* shouldn't happen with unbalance to the right *)
			| node rval rlChild rrChild => 
				match blt_nat (height rlChild) (height rrChild) with
				| true => node rval (node val lChild rlChild) rrChild (* rr *)
				| false => 
					match rlChild with
					| leaf => leaf (* shouldn't happen*)
					| node rlval rllChild rlrChild => 
						node rlval (node val lChild rllChild) (node rval rlrChild rrChild) (* rl *)
					end
				end
			end
		| 4 => (*+2*)
			match lChild with
			| leaf => leaf (* shouldn't happen *)
			| node lval llChild lrChild => 
				match blt_nat (height llChild) (height lrChild) with
				| true => 
					match lrChild with
					| leaf => leaf (* shouldn't happen *)
					| node lrval lrlChild lrrChild => 
						node lrval (node lval llChild lrlChild) (node val lrrChild rChild) (* lr *)
					end
				| false => node lval llChild (node val lrChild rChild) (* ll *)
				end
			end
		| _ => (*Rest should be -1, 0 and +1, which are balanced. Check on the rest of the tree.*)
			node val (balance lChild) (balance rChild)
		end
	end.

Definition insert val t :=
	balance (add val t).

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

Fixpoint inorder (t: tree) :=
	match t with
	| leaf => []
	| node val leftChild rightChild => (inorder leftChild)++val::(inorder rightChild)
	end.

Lemma empty_app : forall (l1: list nat) (l2 : list nat),
	 [] = l1 ++ l2 -> l1 = [] /\ l2 = [].
Proof.
	intros. split. 
		destruct l1. 
			reflexivity. 
			inversion H. 
		destruct l2. 
			reflexivity. 
			destruct l1. 
				inversion H. 
				inversion H.
Qed.

Lemma cons_sorted : forall n l,
	sorted (n::l) -> sorted l.
Proof. 
	intros. inversion H. 
		apply empty. 
		subst. apply H3.
Qed.

Lemma cons_sorted_simpl : forall n l,
	n <= first l -> sorted l -> sorted(n::l).
Proof.
	intros. remember (n::l). induction H0.
	subst. apply single.
	subst. apply more. apply H. apply single.
	subst. apply more. apply H. apply more. apply H0. apply H1.
Qed.

Lemma first_is_first : forall (m: nat) a xs xs',
	m::xs = a::xs' -> m = a.
Proof.
	intros. inversion H. reflexivity.
Qed.

Lemma app_sorted : forall l1 l2,
	last l1 <= first l2 -> sorted l1 -> sorted l2 -> sorted(l1++l2).
Proof. 
	intros. induction H0. simpl in *. assumption.
	destruct l2. simpl in *. apply single. apply more. assumption. assumption.
	simpl. apply more. assumption. apply IHsorted. assumption.
Qed.

Lemma last_is_last : forall a l1 l2,
	last(a::l1) <= first l2 -> last l1 <= first l2.
Proof.
	intros. induction l1. 
		simpl. omega.
		apply H.
Qed.

Lemma last_cons : forall a l1 l2 x xs,
	l1 = x::xs -> last l1 <= first l2 -> a <= first l1 -> last(a::l1) <= first l2.
Proof.
	intros. induction l2.
		simpl in H, H0. destruct l1.
			inversion H1. simpl. omega.
			simpl in H1. inversion H0. auto. 
		destruct l1.
			inversion H1. simpl in *. omega. 
			apply H0.
Qed.

Lemma list_property : forall x y l,
	sorted(x::y::l) -> x <= y.
Proof.
	intros. inversion H. subst. apply H2. 
Qed.

Lemma sorted_property : forall l1 l2,
	l2 <> nil -> sorted (l1++l2) -> last l1 <= first l2.
Proof.
	intros. induction l1.
		simpl. omega.
		simpl in H0. unfold not in H. destruct l2.
			apply ex_falso_quodlibet. apply H. reflexivity.
			simpl in IHl1. destruct l1.
				simpl in *. apply list_property in H0. apply H0.
				simpl in H0. apply last_cons with (x:=n0)(xs:=l1). 
					reflexivity. 
					apply IHl1. simpl in *. apply cons_sorted in H0. apply H0. 
					apply list_property in H0. apply H0.
Qed.

Lemma sorted_app_1 : forall l1 l2,
	sorted (l1++l2) -> sorted (l1).
Proof.
	 intros. remember (l1++l2). generalize dependent l1. induction H. 
	 	intros. apply empty_app in Heql. inversion Heql. rewrite H. apply empty.
	 	destruct l1.
	 		intros. apply empty.
	 		intros. simpl in Heql. inversion Heql. rewrite <- H0. apply empty_app in H1. inversion H1. rewrite H. apply single.
	 	intros.
	 	destruct l1. 
	 		apply empty.
	 		simpl in Heql. inversion Heql. subst. destruct l1.
	 			apply single.
	 			apply more. inversion H3. rewrite <- H2. assumption. apply IHsorted. assumption.
Qed.

Lemma cons_sorted_rev : forall l n,
	sorted(l++[n]) -> sorted l.
Proof.
	intros. inversion H. destruct l. inversion H1. inversion H1. destruct l. 
		apply empty.
		inversion H1. destruct l. inversion H3. inversion H3. destruct l.
			apply empty.
			inversion H0. subst. destruct l.
				apply single. 
				apply more. simpl in H. apply list_property in H. 
				apply H. simpl in H. apply sorted_app_1 with (l1:=n1::n0::l)(l2:=[n]) in H. 
				apply cons_sorted in H. apply H.
Qed.

Lemma concat'_app_sorted : forall n a l1,
	sorted (n :: l1 ++ [a]) -> sorted (n :: l1).
Proof.
	intros. induction l1.
		apply single.
		apply more. simpl in H. apply cons_sorted_rev with (l:=n::a0::l1)(n:=a) in H. apply list_property in H. apply H.
		simpl in H. apply cons_sorted_rev with (l:=n::a0::l1)(n:=a) in H. apply cons_sorted in H. apply H. 
Qed.

Lemma concat_app_sorted : forall n l1 l2,
	sorted (n :: l1 ++ l2) -> sorted (n::l1).
Proof.
	intros. generalize dependent l1. induction l2. 
		intros. rewrite app_nil_r in H. apply H. 
		intros. assert (sorted (n::l1 ++ [a])). apply IHl2. rewrite <- app_assoc. apply H. 
		apply concat'_app_sorted in H0. apply H0. 
Qed.

Lemma concat_app_sorted' : forall n l1 l2,
	sorted (l1 ++ n::l2) -> sorted (n::l2).
Proof.
	intros. induction l1. 
		simpl in H.  apply H. 
		apply IHl1. simpl in H. apply cons_sorted in H. apply H. 
Qed.


Lemma sorted_app: forall l1 l2,
	l2 <> [] -> sorted(l1++l2) -> sorted l1 /\ sorted l2 /\ last l1 <= first l2.
Proof. 
	intros. split.  
		destruct l1. 
			apply empty.
			simpl in H. apply concat_app_sorted in H0. apply H0.
		split.
			destruct l2.
				apply empty.
				apply concat_app_sorted' in H0. apply H0.  
			apply sorted_property in H0. apply H0. apply H.
Qed.

Lemma last_app : forall l n,
	last (l ++ [n]) = last ([n]).
Proof.
	intros. simpl. induction l. 
		reflexivity.
		simpl in *. rewrite IHl. remember (l++[n]) as obviouslynonemptylist. destruct obviouslynonemptylist.
			subst. simpl in *. destruct l. inversion Heqobviouslynonemptylist. inversion Heqobviouslynonemptylist. 
			reflexivity.
Qed.

Lemma last_cons_nonempty : forall e l,
	l <> [] -> last (e::l) = last l.
Proof.
	intros. induction l.
		apply ex_falso_quodlibet. apply H. reflexivity.
		destruct l.
			reflexivity.
			simpl. reflexivity.
Qed.

Lemma last_app_l : forall l1 l2 e,
	last (l1++e::l2) = last (e::l2).
Proof.
	intros. induction l1. 
		reflexivity. 
		destruct l1. 
			reflexivity. 
			simpl. remember (l1 ++ e::l2) as nonemptylist. destruct nonemptylist.
				destruct l1. inversion Heqnonemptylist. inversion Heqnonemptylist.
				rewrite Heqnonemptylist. replace ((n::l1)++e::l2) with (n::l1++e::l2) in IHl1. 
				rewrite last_cons_nonempty with (e:=n)(l:=l1++e::l2) in IHl1. 
				replace (match l2 with | [] => e | _::_ => last l2 end) with (last (e::l2)). rewrite <- IHl1. reflexivity.
				simpl. reflexivity.
				unfold not. intros. destruct l1. inversion H. inversion H.
				reflexivity.
Qed.

Lemma last_lt : forall t e n,
	last (e::inorder t) <= n -> last (inorder t) <= n.
Proof.
	intros. induction t.
		simpl. omega.
		remember (inorder (node n0 t1 t2)) as list. destruct list.
			simpl. omega.
			rewrite last_cons_nonempty in H. apply H. unfold not. intros. inversion H0.
Qed.

Lemma inorder_add_nonempty : forall n t,
	inorder (add n t) <> [].
Proof.
	intros. induction t. 
		simpl. unfold not. intros. inversion H.
		simpl. remember (ble_nat n n0). destruct b. 
			simpl. unfold not. intros. remember (inorder (add n t1)). destruct l. inversion H. inversion H. 
			simpl. unfold not. intros. remember (inorder t1). destruct l. inversion H. inversion H.
Qed.

Lemma last_first_sorted : forall n m t,
	true = ble_nat n m -> last (inorder t) <= m -> last (inorder (add n t)) <= m.
Proof.
	intros. induction t. 
		simpl. symmetry in H. apply ble_nat_true in H. apply H. 
		simpl. remember (ble_nat n n0) as add. destruct add.
			simpl in *. rewrite last_app_l in *. apply H0. 
			simpl in *. rewrite last_app_l in *. rewrite last_cons_nonempty. 
			apply IHt2. apply last_lt in H0. apply H0. apply inorder_add_nonempty. 
Qed.

Lemma sorted_last: forall val leftChild rightChild,
	sorted (inorder (node val leftChild rightChild)) -> last (inorder leftChild ++ val::inorder rightChild) = last (val::inorder rightChild).
Proof.
	intros. inversion H. remember (inorder leftChild). destruct l. inversion H1. inversion H1.
	remember (inorder leftChild). destruct l. inversion H1. reflexivity. inversion H1. destruct l. inversion H3. inversion H3.
	remember (inorder leftChild). destruct l. rewrite H0. simpl. reflexivity. remember (inorder rightChild). destruct l0. rewrite H0. 
	rewrite last_app_l. reflexivity. rewrite H0. rewrite last_app_l. reflexivity.
Qed.


Lemma first_app : forall l1 l2,
	l1 <> [] -> first (l1 ++ l2) = first l1.
Proof.
	intros. destruct l1.
		congruence.
		reflexivity.
Qed.

Lemma inorder_add_property : forall n m t,
	sorted (n::inorder t) -> m > n -> n <= first (inorder (add m t)).
Proof.
	intros. induction t.
		simpl. omega.
		simpl. remember (ble_nat m n0). destruct b.
			simpl. rewrite first_app.  apply IHt1. simpl in H. apply sorted_app with (l1:=n::inorder t1) in H. inversion H. apply H1. 
			congruence. apply inorder_add_nonempty.
			destruct t1.
				simpl in *. apply list_property in H. apply H. 
				simpl in *. rewrite first_app. apply sorted_app with (l1:=n::(inorder t1_1 ++ n1::inorder t1_2)) in H. inversion H.
				remember (inorder t1_1). destruct l. simpl in *. 
				apply list_property in H1. assumption.
				simpl in *. apply list_property in H1. assumption.
				congruence. destruct (inorder t1_1). simpl. congruence. simpl. congruence.
Qed.

Lemma last_cons_le : forall n m l,
	last (n::l) <= m -> last l <= m.
Proof.
	intros. induction l.
		simpl. omega.
		simpl in *. apply H. 
Qed.

Lemma bad_matching_is_bad : forall e1 (e2:nat) l1 (l2: list nat),
	l2 <> [] -> 
	match l1++l2 with 
				| [] => e1 
				| _::_ => e2 
				end  = e2.
Proof.
	intros. destruct l1.
		destruct l2.
			congruence.
			reflexivity.
		reflexivity.
Qed.

Lemma last_inorder : forall n m x t,
	 last (inorder (add n t)) <= m -> last (x :: inorder t) <= m -> last (x :: inorder (add n t)) <= m.
Proof.
	intros. induction t.
		simpl in *. apply H. 
		simpl in *. remember (ble_nat n n0). destruct b; 
			simpl in *; rewrite bad_matching_is_bad in *; rewrite last_app_l in *; try assumption; congruence.
Qed.

Lemma last_add : forall n m t,
	n <= m -> last (inorder t) <= m -> last (inorder (add n t)) <= m.
Proof.
	intros. induction t.
		assumption.
		simpl. remember (ble_nat n n0). destruct b.
			simpl in *. rewrite last_app_l. rewrite last_app_l in H0. assumption.
			simpl in *. rewrite last_app_l. rewrite last_app_l in H0. apply last_inorder. apply IHt2. apply last_cons_le in H0. apply H0. apply H0.
Qed.

Theorem add_preserves_bst': forall n t,
	sorted (inorder t) -> sorted (inorder (add n t)).
Proof.
	intros. induction t. 
		Case "leaf". apply single.
		Case "node". simpl in H. apply sorted_app in H. inversion H. inversion H1. simpl. 
			remember (ble_nat n n0) as add. destruct add. 
				simpl. apply app_sorted; simpl; try apply last_first_sorted; try assumption. apply IHt1. assumption. 
				simpl. apply app_sorted. simpl in *. apply H3. assumption. 
				apply cons_sorted_simpl. apply inorder_add_property. apply H2. symmetry in Heqadd. apply ble_nat_false in Heqadd. omega. 
				apply IHt2. apply cons_sorted in H2. apply H2. congruence. 
Qed.

Lemma blt_nat_false : forall n m,
	blt_nat n m = false -> ~n < m.
Proof.
	intros. induction n. 
		destruct m. omega. inversion H. 
		unfold not, blt_nat in *. apply negb_false_iff in H. intros. apply IHn. apply negb_false_iff. admit. omega.
Qed.

Lemma blt_nat_true : forall n m,
	blt_nat n m = true -> n < m.
Proof.
	intros. induction n. 
		destruct m. 
			inversion H.
			omega. 
		induction m. 
			inversion H. 
			unfold blt_nat in *. simpl in *. apply negb_true_iff in H. admit.
Qed.

Theorem balance_inorder : forall t,
	inorder t = inorder (balance t).
Proof.
	intros. induction t. 
		Case "t = Leaf". reflexivity. 
		Case "t = Node". simpl. remember (height t1 + 2 - height t2) as height1. destruct height1.
			SCase "height1 = 0". destruct t2.
				SSCase "t2 = Leaf". destruct t1. 
					SSSCase "t1 = Leaf". inversion Heqheight1. 
					SSSCase "t1 = Node". inversion Heqheight1.
				SSCase "t2 = Node". remember (blt_nat (height t2_1) (height t2_2)) as height2. destruct height2.
					SSSCase "height2 = true". simpl. repeat rewrite <- app_assoc. simpl. reflexivity. 
					SSSCase "height2 = false". destruct t2_1.
						SSSSCase "t2_1 = Leaf". simpl in Heqheight2. destruct t2_2. simpl in *. omega. simpl in Heqheight2. 
							symmetry in Heqheight2. apply blt_nat_false in Heqheight2. omega.
						SSSSCase "t2_1 = Node". simpl. repeat rewrite <- app_assoc. reflexivity.
			SCase "height1 = S n". destruct height1.
				SSCase "height1' = 0". simpl. rewrite IHt1. rewrite IHt2. reflexivity.
				SSCase "height1' = S n'". destruct height1.
					SSSCase "height1'' = 0". simpl. rewrite IHt1. rewrite IHt2. reflexivity.
					SSSCase "height1'' = S n''". destruct height1.
						SSSSCase "height1''' = 0". simpl. rewrite IHt1, IHt2. reflexivity.
						SSSSCase "height1''' = S n'''". simpl. destruct height1.
							SSSSSCase "height1'''' = 0". destruct t1.
								SSSSSSCase "t1 = Leaf". simpl in Heqheight1. remember (height t2). 
									destruct n0. inversion Heqheight1. destruct n0. inversion Heqheight1. inversion Heqheight1. 
								SSSSSSCase "t1 = Node". remember (blt_nat (height t1_1) (height t1_2)) as height3. destruct height3.
									SSSSSSSCase "height3 = true". destruct t1_2. 
										(*t1_2 = Leaf*) simpl in Heqheight3. symmetry in Heqheight3. 
											apply blt_nat_true in Heqheight3. inversion Heqheight3.
										(*t1_2 = Node*) simpl. repeat rewrite <- app_assoc. simpl. rewrite <- app_assoc. reflexivity.
									SSSSSSSCase "height3 = false". simpl. rewrite <- app_assoc. reflexivity.
							SSSSSCase "height1'''' = S n''''". simpl. rewrite IHt1, IHt2. reflexivity.
Qed.

Theorem insert_preserves_bst : forall n t,
	sorted (inorder t) -> sorted (inorder (insert n t)).
Proof.
	intros. unfold insert. rewrite <- balance_inorder. apply add_preserves_bst'. assumption. 
Qed.

(*induction t. 
		Case "t Leaf". simpl. apply single.
		Case "t Node". simpl in H. apply sorted_app in H. inversion H. inversion H1. unfold insert. simpl in *. remember (ble_nat n n0) as add. 
		destruct add. 
			SCase "Add left tree". simpl. remember (height (add n t1) + 2 - height t2) as height1. destruct height1.
				SSCase "height1 = 0". destruct t2. 
					SSSCase "t2 Leaf". simpl. apply empty.
					SSSCase "t2 Node". remember (height t2_1 + 2 - height t2_2) as height2. destruct height2.
						SSSSCase "height2 = 0". destruct t2_1.
							SSSSSCase "t2_1 Leaf". apply empty.
							SSSSSCase "t2_1 Node". simpl. apply app_sorted. 
								SSSSSSCase "app_sorted 1". simpl in *. destruct t2_1_1.
									SSSSSSSCase "t2_1_1 Leaf". simpl in *. rewrite last_app. simpl. apply list_property in H2. apply H2. 
									SSSSSSSCase "t2_1_1 Node". 
										simpl. rewrite last_app_l. 
										replace (n0 :: inorder t2_1_1_1 ++ n3 :: inorder t2_1_1_2) 
											with ((n0 :: inorder t2_1_1_1) ++ n3 :: inorder t2_1_1_2).
											rewrite last_app_l with (l1:=n0::inorder t2_1_1_1). 
											apply cons_sorted in H2.
											apply sorted_app in H2. 
												inversion H2. subst. apply sorted_app in H4. 
													inversion H4.
													apply sorted_last in H6. inversion H7. simpl in H9. rewrite <- H6. apply H9. 
												congruence.
											congruence.
										reflexivity.
								SSSSSSCase "app_sorted 2". apply app_sorted. 
									SSSSSSSCase "app_sorted 2_1". simpl. apply last_add. 
										symmetry in Heqadd. apply ble_nat_true in Heqadd. assumption. assumption.
									SSSSSSSCase "app_sorted 2_2". apply add_preserves_bst'. assumption.
									SSSSSSSCase "app_sorted 2_3". simpl in H2. 
										replace (n0 :: (inorder t2_1_1 ++ n2 :: inorder t2_1_2) ++ n1 :: inorder t2_2) 
											with (n0 :: inorder t2_1_1 ++ n2 :: inorder t2_1_2 ++ n1 :: inorder t2_2) in H2.
										apply sorted_app with (l1:=n0::inorder t2_1_1) in H2. 
											inversion H2. apply H4. 
										congruence. 
									rewrite <- app_assoc. reflexivity. 
								SSSSSSCase "app_sorted 3". simpl in H2. apply cons_sorted in H2. rewrite <- app_assoc in H2. 
									apply sorted_app in H2.
										inversion H2.
											inversion H5. apply H6. 
										simpl. congruence.
									SSSSCase "height2 = S n". destruct height2.
										SSSSSCase "height2' = 0". simpl. apply app_sorted. 
											SSSSSSCase "app_sorted 1". 
												simpl. rewrite last_app_l. simpl in H2. apply sorted_app with (l1:=n0::inorder t2_1) in H2. 
													inversion H2. inversion H5. apply H7. congruence. 
											SSSSSSCase "app_sorted 2". simpl in H2. apply sorted_app with (l1:=n0::inorder t2_1) in H2. 
												inversion H2. apply app_sorted. 
													SSSSSSSCase "app_sorted 2_1". simpl. apply last_add. symmetry in Heqadd. 
														apply ble_nat_true in Heqadd. assumption. assumption.
													SSSSSSSCase "app_sorted 2_2". apply add_preserves_bst'. assumption. 
													SSSSSSSCase "app_sorted 2_3". assumption.
													congruence.
											SSSSSSCase "app_sorted 3". simpl in H2. 
												apply sorted_app with (l1:=n0::inorder t2_1)(l2:=n1::inorder t2_2) in H2. 
													inversion H2.
													inversion H5. apply H6. congruence.
										SSSSSCase "height2' = S n'". destruct t2_1. 
											SSSSSSCase "t2_1 Leaf". apply empty. 
											SSSSSSCase "t2_1 Node".	simpl. apply app_sorted. 
												SSSSSSSCase "app_sorted 1". simpl. rewrite last_app_l.
													simpl in H2. rewrite <- app_assoc in H2. apply sorted_app with (l1:=n0::inorder t2_1_1) in H2.
													inversion H2. inversion H5. apply H7. simpl. congruence.
												SSSSSSSCase "app_sorted 2". apply app_sorted.
													simpl. apply last_add. symmetry in Heqadd. apply ble_nat_true in Heqadd. omega. assumption.
													apply add_preserves_bst'. assumption. simpl in H2. rewrite <- app_assoc in H2. 
													apply sorted_app with (l1:=n0::inorder t2_1_1) in H2. inversion H2. inversion H5. assumption.
													simpl. congruence.
												SSSSSSSCase "app_sorted 3". simpl in H2. rewrite <- app_assoc in H2. 
													apply sorted_app with (l1:=n0::inorder t2_1_1) in H2. inversion H2. inversion H5. assumption.
													simpl. congruence.
										SSCase "height1 = S n". destruct height1.
												SSSCase "height1' = 0". simpl. apply app_sorted. 
													SSSSCase "app_sorted 1". simpl. admit.
													SSSSCase "app_sorted 2". admit.
													SSSSCase "app_sorted 3". admit.
												SSSCase "height1' = S n'". destruct height1. 
													SSSSCase "height1'' = 0". simpl. admit.
													SSSSCase "height1'' = S n''". destruct height1.
														SSSSSCase "height1''' = 0". simpl. admit.
														SSSSSCase "height1''' = S n'''". destruct height1. 
															SSSSSSCase "height1'''' = 0".
																remember (add n t1) as nt1. destruct nt1.
																	SSSSSSSCase "nt1 Leaf". apply empty.
																	SSSSSSSCase "nt1 Node".
																		remember (height nt1_1 + 2 - height nt1_2) as height3. 
																		destruct height3.
																			(*height3 = 0*)simpl. apply app_sorted. 
																				(*app_sorted 1*) simpl. admit.
																				(*app_sorted 2*) admit.
																				(*app_sorted 3*) admit.
																			(*height3 = S n*)destruct height3.
																				(*height3' = 0*)destruct nt1_2.
																					(*nt1_2 = Leaf*)apply empty.
																					(*nt1_2 = Node*)simpl. admit.
																				(*height3' = S n'*)simpl. admit.
															SSSSSSCase "height1'''' = S n''''".
																simpl. apply app_sorted. 
																	SSSSSSSCase "app_sorted 1". simpl. admit.
																	SSSSSSSCase "app_sorted 2". admit.
																	SSSSSSSCase "app_sorted 3". admit.
			SCase "Add right tree".
				simpl. remember (height t1 + 2 - height (add n t2)) as height4. destruct height4.
					SSCase "height4 = 0". remember (add n t2) as nt2. destruct nt2.
						SSSCase "nt2 = Leaf". apply empty.
						SSSCase "nt2 = Node". 
							remember (height nt2_1 + 2 - height nt2_2) as height5. destruct height5.
								SSSSCase "height5 = 0". destruct nt2_1.
									SSSSSCase "nt2_1 = Leaf". apply empty.
									SSSSSCase "nt2_1 = Node". simpl. admit.
								SSSSCase "height5 = S n". destruct height5.
									SSSSSCase "height5' = 0". simpl. admit.
									SSSSSCase "height5' = S n'". destruct nt2_1.
										SSSSSSCase "nt2_1 = Leaf". apply empty.
										SSSSSSCase "nt2_1 = Node". simpl. admit.
					SSCase "height4 = S n". destruct height4.
						SSSCase "height4' = 0". simpl. admit.
						SSSCase "height4' = S n'". destruct height4.
							SSSSCase "height4'' = 0". simpl. admit.
							SSSSCase "height4'' = S n''". destruct height4.
								SSSSSCase "height4''' = 0". simpl. admit.
								SSSSSCase "height4''' = S n'''". destruct height4.
									SSSSSSCase "height4'''' = 0". destruct t1.
										SSSSSSSCase "t1 = Leaf". apply empty.
										SSSSSSSCase "t1 = Node". remember (height t1_1 + 2 - height t1_2) as height6. destruct height6.
											(*height6 = 0*) simpl. admit.
											(*height6 = S n*)destruct height6.
												(*height6' = 0*)destruct t1_2.
													(*t1_2 = Leaf*)apply empty.
													(*t1_2 = Node*)simpl. admit.
												(*height6' = S n'*)simpl. admit.
									SSSSSSCase "height4'''' = S n''''". simpl. admit.
	congruence.	
Qed.*)

Theorem insert_preserves_balance: forall n t t',
	t = insert n t' ->height t <= log2 (length (inorder t') + 1) + 1 = true.
Proof. 
	intros. induction t'.
		Case "leaf". rewrite H. reflexivity.
		Case "node". simpl in *. rewrite H. destruct t'1. destruct t'2. simpl. admit. simpl.

Qed.