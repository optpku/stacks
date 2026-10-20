module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-! # Finite intersections of open subspaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The intersection of two open subspaces, realized as the pullback of their inclusions. -/
noncomputable def OpenSubspace.inf {F : AlgebraicSpace S} (U V : OpenSubspace F) :
    OpenSubspace F where
  X := pullback U.ι V.ι
  ι := pullback.fst U.ι V.ι ≫ U.ι
  isOpenImmersion := sorry

/-- The inclusion of an intersection factors through the first open subspace. -/
theorem OpenSubspace.inf_ι_fst {F : AlgebraicSpace S} (U V : OpenSubspace F) :
    (U.inf V).ι = pullback.fst U.ι V.ι ≫ U.ι :=
  rfl

/-- Fold the open subspaces `V j` onto an accumulator by successive intersections,
starting from the last index. -/
noncomputable def OpenSubspace.infLast {F : AlgebraicSpace S} (n : ℕ)
    (V : Fin n → OpenSubspace F) (acc : OpenSubspace F) : OpenSubspace F :=
  match n with
  | 0 => acc
  | n + 1 =>
    (OpenSubspace.infLast n (fun j => V j.castSucc) acc).inf (V (Fin.last n))

/-- The intersection of a finite family of open subspaces indexed by pairs `j < i`. -/
noncomputable def OpenSubspace.infFamily {F : AlgebraicSpace S} (n : ℕ)
    (U : (i : Fin n) → (j : Fin i.val) → OpenSubspace F) : OpenSubspace F :=
  match n with
  | 0 => OpenSubspace.id F
  | n + 1 =>
    OpenSubspace.infLast n (fun j => U (Fin.last n) j)
      (OpenSubspace.infFamily n fun i j => U i.castSucc j)

/-- Compatible lifts of an ambient map induce a map into a finite intersection. -/
noncomputable def OpenSubspace.infLastLift {T F : AlgebraicSpace S} (n : ℕ)
    (V : Fin n → OpenSubspace F) (acc : OpenSubspace F) (h : T ⟶ F)
    (liftAcc : T ⟶ acc.X) (hAcc : liftAcc ≫ acc.ι = h)
    (liftsV : (j : Fin n) → (T ⟶ (V j).X))
    (hV : ∀ j, liftsV j ≫ (V j).ι = h) : T ⟶ (OpenSubspace.infLast n V acc).X :=
  match n with
  | 0 => liftAcc
  | n + 1 =>
    pullback.lift
      (OpenSubspace.infLastLift n (fun j => V j.castSucc) acc h liftAcc hAcc
        (fun j => liftsV j.castSucc) (fun j => hV j.castSucc))
      (liftsV (Fin.last n)) sorry

/-- Compatible lifts of an ambient map induce a map into a pair-indexed intersection. -/
noncomputable def OpenSubspace.infFamilyLift {T F : AlgebraicSpace S} (n : ℕ)
    (U : (i : Fin n) → (j : Fin i.val) → OpenSubspace F) (h : T ⟶ F)
    (lifts : (i : Fin n) → (j : Fin i.val) → (T ⟶ (U i j).X))
    (hL : ∀ i j, lifts i j ≫ (U i j).ι = h) :
    T ⟶ (OpenSubspace.infFamily n U).X :=
  match n with
  | 0 => h
  | n + 1 =>
    OpenSubspace.infLastLift n (fun j => U (Fin.last n) j)
      (OpenSubspace.infFamily n fun i j => U i.castSucc j) h
      (OpenSubspace.infFamilyLift n (fun i j => U i.castSucc j) h
        (fun i j => lifts i.castSucc j) (fun i j => hL i.castSucc j)) sorry
      (fun j => lifts (Fin.last n) j) (fun j => hL (Fin.last n) j)

/-- The inclusion of a compatible finite-intersection lift is its ambient map. -/
theorem OpenSubspace.infLastLift_comp {T F : AlgebraicSpace S} (n : ℕ)
    (V : Fin n → OpenSubspace F) (acc : OpenSubspace F) (h : T ⟶ F)
    (liftAcc : T ⟶ acc.X) (hAcc : liftAcc ≫ acc.ι = h)
    (liftsV : (j : Fin n) → (T ⟶ (V j).X)) (hV : ∀ j, liftsV j ≫ (V j).ι = h) :
    OpenSubspace.infLastLift n V acc h liftAcc hAcc liftsV hV ≫
      (OpenSubspace.infLast n V acc).ι = h :=
  sorry

/-- The inclusion of a compatible pair-indexed intersection lift is its ambient map. -/
theorem OpenSubspace.infFamilyLift_comp {T F : AlgebraicSpace S} (n : ℕ)
    (U : (i : Fin n) → (j : Fin i.val) → OpenSubspace F) (h : T ⟶ F)
    (lifts : (i : Fin n) → (j : Fin i.val) → (T ⟶ (U i j).X))
    (hL : ∀ i j, lifts i j ≫ (U i j).ι = h) :
    OpenSubspace.infFamilyLift n U h lifts hL ≫ (OpenSubspace.infFamily n U).ι = h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
