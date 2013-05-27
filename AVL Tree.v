Require Export SfLib.

Definition blt_nat n1 n2 :=
	negb (ble_nat n2 n1).
	
Lemma not_lt_S : forall n m,
	(~ n < m) -> (~ S n < S m).
Proof.
	intros. unfold not in *. intros. apply H. omega.
Qed.

Lemma blt_nat_false : forall n m,
	blt_nat n m = false -> ~(n < m).
Proof. 
	induction n. 
		intros. destruct m. 
			omega. 
			inversion H. 
		intros. destruct m.
			omega. 
			apply not_lt_S. apply IHn. replace (blt_nat n m = false) with (blt_nat (S n) (S m) = false). apply H.
				unfold blt_nat. simpl. reflexivity.
Qed.

Lemma blt_nat_true : forall n m,
	blt_nat n m = true -> n < m.
Proof.
	induction n.
		destruct m.
			intros. unfold blt_nat in H. simpl in H. inversion H.
			intros. omega.
		destruct m.
			intros. unfold blt_nat in H. simpl in H. inversion H.
			intros. apply lt_n_S. apply IHn. unfold blt_nat in *. apply negb_true_iff. apply negb_true_iff in H. simpl in H. assumption.
Qed.

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
	| node : nat -> nat -> tree -> tree -> tree.
	        (* Value -> height -> Left -> Right *)

Inductive sorted : list nat -> Prop :=
	| s_nil : sorted []
	| s_single : forall n, sorted [n]
	| s_cons : forall n m xs, n <= m -> sorted (m::xs) -> sorted (n::m::xs).

	
Fixpoint max n m {struct n} : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

(* O(1) *)
Fixpoint height t :=
  match t with
  | leaf => 0
  | node _ h _ _ => h
  end.

Fixpoint height_calc t :=
  match t with
  | leaf => 0
  | node _ _ LC RC => 1 + max (height_calc LC) (height_calc RC)
  end.

(* O(1), but requires sub-tree height to be valid (add should ensure this) *)
Fixpoint updateHeight t :=
  match t with
  | leaf => leaf
  | node val _ LC RC => node val (1 + max (height LC) (height RC)) LC RC
  end.

(* O(log n) for avl, O(n) for bst *)
Fixpoint add v t :=
  match t with
  | leaf => node v 1 leaf leaf
  | node val _ LC RC => 
    match ble_nat v val with
    | true => match (updateHeight (add v LC)) with
       | addLC => node val (1 + max (height addLC) (height RC)) addLC RC
       end
    | false => match (updateHeight (add v RC)) with
      | addRC => node val (1 + max (height LC) (height addRC)) LC addRC
      end
    end
  end.

Fixpoint balance (t : tree) :=
	match t with
	| leaf => leaf (*Leaf tree is already balanced*)
	| node val h lChild rChild => 
		match (height lChild) + 2 - (height rChild) with
		| 0 => (*-2, unbalanced to the right*)
			match rChild with
			| leaf => leaf (* shouldn't happen with unbalance to the right *)
			| node rval rh rlChild rrChild => 
				match blt_nat (height rlChild) (height rrChild) with
				| true => node rval rh (node val (h-2) lChild rlChild) rrChild (* rr *)
				| false => 
					match rlChild with
					| leaf => leaf (* shouldn't happen*)
					| node rlval rlh rllChild rlrChild => 
						node rlval (rlh+1) (node val (h-2) lChild rllChild) (node rval (rh-1) rlrChild rrChild) (* rl *)
					end
				end
			end
		| 4 => (*+2*)
			match lChild with
			| leaf => leaf (* shouldn't happen *)
			| node lval lh llChild lrChild => 
				match blt_nat (height llChild) (height lrChild) with
				| true => 
					match lrChild with
					| leaf => leaf (* shouldn't happen *)
					| node lrval lrh lrlChild lrrChild => 
						node lrval (lrh+1) (node lval (lh-1) llChild lrlChild) (node val (h-2) lrrChild rChild) (* lr *)
					end
				| false => node lval lh llChild (node val (h-2) lrChild rChild) (* ll *)
				end
			end
		| _ => (*Rest should be -1, 0 and +1, which are balanced. Check on the rest of the tree.*)
			node val h (balance lChild) (balance rChild)
		end
	end.

Definition insert val t :=
	balance (add val t).


Fixpoint inorder (t: tree) :=
	match t with
	| leaf => []
	| node val _ leftChild rightChild => (inorder leftChild)++val::(inorder rightChild)
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
		apply s_nil. 
		subst. apply H3.
Qed.

Lemma sorted_cons : forall n l,
	n <= first l -> sorted l -> sorted(n::l).
Proof.
	intros. remember (n::l). induction H0.
	subst. apply s_single.
	subst. apply s_cons. apply H. apply s_single.
	subst. apply s_cons. apply H. apply s_cons. apply H0. apply H1.
Qed.

Lemma app_sorted : forall l1 l2,
	last l1 <= first l2 -> sorted l1 -> sorted l2 -> sorted(l1++l2).
Proof. 
	intros. induction H0. simpl in *. assumption.
	destruct l2. simpl in *. apply s_single. simpl. apply s_cons. assumption. assumption.
	simpl. apply s_cons. assumption. apply IHsorted. assumption.
Qed.

Lemma last_cons : forall e l,
	l <> [] -> last (e::l) = last l.
Proof.
	intros. induction l.
		apply ex_falso_quodlibet. apply H. reflexivity.
		destruct l.
			reflexivity.
			simpl. reflexivity.
Qed.

Lemma s_cons_rev : forall x y l,
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
				simpl in *. apply s_cons_rev in H0. apply H0.
				simpl in H0. rewrite last_cons. apply IHl1. simpl in *. apply cons_sorted in H0. apply H0. 
					apply s_cons_rev in H0. congruence.
Qed.

Lemma sorted_app_l1 : forall l1 l2,
	sorted (l1++l2) -> sorted (l1).
Proof.
	 intros. remember (l1++l2). generalize dependent l1. induction H. 
	 	intros. apply empty_app in Heql. inversion Heql. rewrite H. apply s_nil.
	 	destruct l1.
	 		intros. apply s_nil.
	 		intros. simpl in Heql. inversion Heql. rewrite <- H0. apply empty_app in H1. inversion H1. rewrite H. apply s_single.
	 	intros.
	 	destruct l1. 
	 		apply s_nil.
	 		simpl in Heql. inversion Heql. subst. destruct l1.
	 			apply s_single.
	 			apply s_cons. inversion H3. rewrite <- H2. assumption. apply IHsorted. assumption.
Qed.

Lemma sorted_app_l2 : forall l1 l2,
	sorted (l1++l2) -> sorted l2.
Proof.
	intros. remember (l1++l2). generalize dependent l1. induction H.
		intros. apply empty_app in Heql. inversion Heql. rewrite H0. apply s_nil.
		destruct l1.
			intros. simpl in Heql. rewrite <- Heql. apply s_single.
			intros. simpl in Heql. inversion Heql. apply empty_app in H1. inversion H1. subst. apply s_nil.
		intros. destruct l2.  
 				 apply s_nil.
 				 destruct l1.
 				 	simpl in *. rewrite <- Heql. apply s_cons. assumption. assumption.
 				 	inversion Heql. subst. simpl in *. inversion Heql. apply IHsorted with (l1:=l1). assumption.
Qed.

Lemma sorted_app: forall l1 l2,
	l2 <> [] -> sorted(l1++l2) -> sorted l1 /\ sorted l2 /\ last l1 <= first l2.
Proof. 
	intros. split.  
		destruct l1. 
			apply s_nil.
			simpl in H. apply sorted_app_l1 in H0. apply H0.
		split.
			destruct l2.
				apply s_nil.
				apply sorted_app_l2 in H0. apply H0.  
			apply sorted_property in H0. apply H0. apply H.
Qed.

Lemma obvious_match : forall e1 (e2:nat) l1 (l2: list nat),
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

Lemma last_app : forall l1 l2,
	l2 <> [] -> last (l1 ++ l2) = last l2.
Proof.
	intros. induction l1.
		reflexivity.
		simpl in *. rewrite obvious_match. apply IHl1. assumption.			
Qed.

Lemma first_app : forall l1 l2,
	l1 <> [] -> first (l1 ++ l2) = first l1.
Proof.
	intros. destruct l1.
		congruence.
		reflexivity.
Qed.

Lemma last_lt : forall t e n,
	last (e::inorder t) <= n -> last (inorder t) <= n.
Proof.
	intros. induction t.
		simpl. omega.
		remember (inorder (node n0 n1 t1 t2)) as list. destruct list.
			simpl. omega.
			rewrite last_cons in H. apply H. unfold not. intros. inversion H0.
Qed.

Lemma inorder_add_nonempty : forall n t,
	inorder (add n t) <> [].
Proof.
	intros. induction t. 
		simpl. unfold not. intros. inversion H.
		simpl. remember (ble_nat n n0). destruct b. 
			simpl. unfold not. intros. remember (inorder (updateHeight (add n t1))). destruct l. inversion H. inversion H. 
			simpl. unfold not. intros. remember (inorder t1). destruct l. inversion H. inversion H.
Qed.

Lemma sorted_last: forall val h leftChild rightChild,
	sorted (inorder (node val h leftChild rightChild)) -> last (inorder leftChild ++ val::inorder rightChild) = last (val::inorder rightChild).
Proof.
	intros. inversion H. remember (inorder leftChild). destruct l. inversion H1. inversion H1.
	remember (inorder leftChild). destruct l. inversion H1. reflexivity. inversion H1. destruct l. inversion H3. inversion H3.
	remember (inorder leftChild). destruct l. rewrite H0. simpl. reflexivity. remember (inorder rightChild). destruct l0. rewrite H0. 
	rewrite last_app. reflexivity. congruence. rewrite H0. rewrite last_app. reflexivity. congruence.
Qed.

Lemma last_cons_le : forall n m l,
	last (n::l) <= m -> last l <= m.
Proof.
	intros. induction l.
		simpl. omega.
		simpl in *. apply H. 
Qed.

Lemma update_preserves_structure : forall t,
	inorder t = inorder (updateHeight t).
Proof.
	intros. induction t; simpl; reflexivity.
Qed.

Lemma add_le : forall n m t,
	n <= m -> last (inorder t) <= m -> last (inorder (add n t)) <= m.
Proof.
	intros. induction t. 
		simpl. apply H. 
		simpl. remember (ble_nat n n0) as add. destruct add.
			simpl in *. rewrite <- update_preserves_structure. rewrite last_app in *; try apply H0; congruence.
			simpl in *. rewrite <- update_preserves_structure. rewrite last_app in *; try rewrite last_cons; 
			try apply IHt2; try apply last_lt in H0; try assumption; try congruence. apply inorder_add_nonempty. 
Qed.

Lemma inorder_add_property : forall n m t,
	sorted (n::inorder t) -> m > n -> n <= first (inorder (add m t)).
Proof.
	intros. induction t.
		simpl. omega.
		simpl. remember (ble_nat m n0). destruct b.
			simpl. rewrite <- update_preserves_structure. rewrite first_app.  apply IHt1. simpl in H. apply sorted_app with (l1:=n::inorder t1) in H. 
				inversion H. apply H1. 
			congruence. apply inorder_add_nonempty.
			simpl. destruct t1.
				simpl in *. apply s_cons_rev in H. apply H. 
				simpl in *. rewrite first_app. apply sorted_app with (l1:=n::(inorder t1_1 ++ n2::inorder t1_2))(l2:=n0::inorder t2) in H. inversion H.
				remember (inorder t1_1). destruct l. simpl in *. 
				apply s_cons_rev in H1. assumption.
				simpl in *. apply s_cons_rev in H1. assumption.
				congruence. destruct (inorder t1_1). simpl. congruence. simpl. congruence.
Qed. 

Theorem add_preserves_bst: forall n t,
	sorted (inorder t) -> sorted (inorder (add n t)).
Proof.
	intros. induction t. 
		Case "leaf". simpl. apply s_single.
		Case "node". simpl in H. apply sorted_app in H. inversion H. inversion H1. simpl. 
			remember (ble_nat n n0) as add. destruct add. 
				simpl. rewrite <- update_preserves_structure. apply app_sorted. simpl in *. apply add_le. symmetry in Heqadd. apply ble_nat_true in Heqadd.
					assumption. assumption. apply IHt1. assumption. assumption.
				simpl. rewrite <- update_preserves_structure. apply app_sorted. simpl in *. apply H3. assumption. 
				apply sorted_cons. apply inorder_add_property. apply H2. symmetry in Heqadd. apply ble_nat_false in Heqadd. omega. 
				apply IHt2. apply cons_sorted in H2. apply H2. congruence. 
Qed.

Lemma height_heightcalc : forall t,
	height t = height_calc t. (* Definately not true for all random trees, but should be the case for trees only generated by add... *)
Proof.
	intros. induction t. 
		reflexivity.
		simpl. admit.
Qed.

Theorem balance_inorder : forall t,
	inorder t = inorder (balance t).
Proof.
	intros. induction t. 
		Case "t = Leaf". reflexivity. 
		Case "t = Node". simpl. remember (height t1 + 2 - height t2) as height1. destruct height1.
			SCase "height1 = 0". destruct t2.
				SSCase "t2 = Leaf". destruct (height t1); inversion Heqheight1. 
				SSCase "t2 = Node". remember (blt_nat (height t2_1) (height t2_2)) as height2. destruct height2.
					SSSCase "height2 = true". simpl. repeat rewrite <- app_assoc. simpl. reflexivity. 
					SSSCase "height2 = false". destruct t2_1.
						SSSSCase "t2_1 = Leaf". destruct t2_2. 
							rewrite height_heightcalc with (t:=node n1 n2 leaf leaf) in Heqheight1. simpl in Heqheight1. omega. 
							repeat rewrite height_heightcalc in *. simpl in Heqheight1, Heqheight2. 
								symmetry in Heqheight2. apply blt_nat_false in Heqheight2. 
								remember (max (height_calc t2_2_1) (height_calc t2_2_2)). destruct n5.
									unfold not in Heqheight2. apply ex_falso_quodlibet. apply Heqheight2. omega. 
									unfold not in Heqheight2. apply ex_falso_quodlibet. apply Heqheight2. omega. 
						SSSSCase "t2_1 = Node". simpl. repeat rewrite <- app_assoc. reflexivity.
			SCase "height1 = S n". destruct height1.
				SSCase "height1' = 0". simpl. rewrite IHt1. rewrite IHt2. reflexivity.
				SSCase "height1' = S n'". destruct height1.
					SSSCase "height1'' = 0". simpl. rewrite IHt1. rewrite IHt2. reflexivity.
					SSSCase "height1'' = S n''". destruct height1.
						SSSSCase "height1''' = 0". simpl. rewrite IHt1, IHt2. reflexivity.
						SSSSCase "height1''' = S n'''". destruct height1.
							SSSSSCase "height1'''' = 0". destruct t1.
								SSSSSSCase "t1 = Leaf". simpl in Heqheight1. remember (height t2). 
									destruct n1. inversion Heqheight1. destruct n1. inversion Heqheight1. inversion Heqheight1. 
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
	intros. unfold insert. rewrite <- balance_inorder. apply add_preserves_bst. assumption. 
Qed.