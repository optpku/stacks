module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Group.ULift
public import Mathlib.GroupTheory.Perm.Sign
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero
public import stacks_project.Chap69.Lemma_69_6_1_ExtensionByZero
public import stacks_project.Chap69.Lemma_69_6_3_DerivedSections
public import stacks_project.Chap69.Lemma_69_6_4_FibrePower

/-!
# Off-diagonal fibre products and permutation anti-invariants

The open-and-closed subspace `W ⊂ U^n` obtained by deleting all pairwise diagonals
carries an `Equiv.Perm (Fin n)`-action over `X`. Anti-invariants of an abelian group
with this signed action are the `S_n`-anti-invariant elements.
-/

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

/-- Intersection of the open complements of all pairwise diagonals in a family indexed
by `j < i`. -/
noncomputable def OpenSubspace.infFamily {F : AlgebraicSpace S} (n : ℕ)
    (U : (i : Fin n) → (j : Fin i.val) → OpenSubspace F) : OpenSubspace F :=
  match n with
  | 0 => OpenSubspace.id F
  | n + 1 =>
    OpenSubspace.infLast n (fun j => U (Fin.last n) j)
      (OpenSubspace.infFamily n fun i j => U i.castSucc j)

/-- A map into `X` that misses `|Z|` factors through the open complement of a
closed immersion `i : Z ⟶ X`, via the missing-closed-image subfunctor. -/
noncomputable def closedImmersionComplementLift {T X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (α : T ⟶ X)
    (h : ∀ (U : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj U),
      missesClosedImage i (α.app U t)) :
    T ⟶ closedImmersionComplement i where
  app U := TypeCat.ofHom fun t ↦ ⟨α.app U t, h U t⟩
  naturality := sorry

/-- The lifted map to the complement composes to the original map into `X`. -/
theorem closedImmersionComplementLift_comp {T X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (α : T ⟶ X)
    (h : ∀ (U : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj U),
      missesClosedImage i (α.app U t)) :
    closedImmersionComplementLift i α h ≫ closedImmersionComplementι i = α :=
  sorry

/-- Lift a map through a running intersection of open subspaces `V j`. -/
noncomputable def OpenSubspace.infLastLift {T F : AlgebraicSpace S} (n : ℕ)
    (V : Fin n → OpenSubspace F) (acc : OpenSubspace F) (liftAcc : T ⟶ acc.X)
    (liftsV : (j : Fin n) → (T ⟶ (V j).X)) : T ⟶ (OpenSubspace.infLast n V acc).X :=
  match n with
  | 0 => liftAcc
  | n + 1 =>
    pullback.lift
      (OpenSubspace.infLastLift n (fun j => V j.castSucc) acc liftAcc
        fun j => liftsV j.castSucc)
      (liftsV (Fin.last n)) sorry

/-- Lift a map through the intersection of a pairwise-indexed family of open subspaces. -/
noncomputable def OpenSubspace.infFamilyLift {T F : AlgebraicSpace S} (n : ℕ)
    (U : (i : Fin n) → (j : Fin i.val) → OpenSubspace F) (h : T ⟶ F)
    (lifts : (i : Fin n) → (j : Fin i.val) → (T ⟶ (U i j).X)) :
    T ⟶ (OpenSubspace.infFamily n U).X :=
  match n with
  | 0 => h
  | n + 1 =>
    OpenSubspace.infLastLift n (fun j => U (Fin.last n) j)
      (OpenSubspace.infFamily n fun i j => U i.castSucc j)
      (OpenSubspace.infFamilyLift n (fun i j => U i.castSucc j) h
        fun i j => lifts i.castSucc j)
      fun j => lifts (Fin.last n) j

/-- The open complement of the pairwise diagonal `Δ_{ij}` inside the `n`-fold fibre
product of `f`. -/
noncomputable def pairwiseDiagonalComplement {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] {n : ℕ} (i j : Fin n) : OpenSubspace (selfFibrePower f n) :=
  closedImmersionComplementSubspace (pairwiseDiagonalι f i j)

/-- Pairwise diagonal complements, reindexed by strictly ordered pairs `j < i`. -/
noncomputable def pairwiseDiagonalComplementFamily {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (n : ℕ) (i : Fin n) (j : Fin i.val) :
    OpenSubspace (selfFibrePower f n) :=
  pairwiseDiagonalComplement f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i

/-- The open subspace of the `n`-fold fibre product of `f` obtained by deleting all
pairwise diagonals. -/
noncomputable def offDiagonalSubspace {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : OpenSubspace (selfFibrePower f n) :=
  OpenSubspace.infFamily n (pairwiseDiagonalComplementFamily f n)

/-- The algebraic space `W` obtained from the `n`-fold fibre product of `f` by deleting
all pairwise diagonals. For `n = p + 1` this is the source space `W_p`. -/
noncomputable def offDiagonal {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    AlgebraicSpace S :=
  (offDiagonalSubspace f n).X

/-- The open inclusion of the off-diagonal locus into the `n`-fold fibre product. -/
noncomputable def offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    offDiagonal f n ⟶ selfFibrePower f n :=
  (offDiagonalSubspace f n).ι

/-- The structure morphism `W ⟶ X` of the off-diagonal locus. -/
noncomputable def offDiagonalToBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : offDiagonal f n ⟶ X :=
  offDiagonalι f n ≫ selfFibrePowerToBase f n

/-- The off-diagonal inclusion is the inclusion of the folded open subspace. -/
theorem offDiagonalι_eq {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    offDiagonalι f n = (offDiagonalSubspace f n).ι :=
  rfl

/-- The structure morphism of the off-diagonal locus is the composite of the open
inclusion with the fibre-power structure morphism. -/
theorem offDiagonalToBase_eq {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    offDiagonalToBase f n = offDiagonalι f n ≫ selfFibrePowerToBase f n :=
  rfl

/-- The off-diagonal inclusion is an open immersion. -/
instance instIsOpenImmersion_offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) : IsOpenImmersion (offDiagonalι f n) :=
  (offDiagonalSubspace f n).isOpenImmersion

/-- If `f` is étale and separated, the structure morphism of the off-diagonal locus is
étale. -/
instance instEtale_offDiagonalToBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) : Etale (offDiagonalToBase f n) :=
  sorry

/-- The off-diagonal inclusion is étale. -/
instance instEtale_offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : Etale (offDiagonalι f n) :=
  Etale.ofIsOpenImmersion

/-- If `f` is étale and separated, the off-diagonal inclusion is a closed immersion. -/
public instance instIsClosedImmersion_offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) : IsClosedImmersion (offDiagonalι f n) :=
  sorry

/-- The closed complement of `W` in the `n`-fold fibre product, i.e. the union of all
pairwise diagonals. -/
noncomputable def offDiagonalRest {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) : AlgebraicSpace S :=
  closedImmersionComplement (offDiagonalι f n)

/-- The inclusion of the union of pairwise diagonals into the fibre product. -/
noncomputable def offDiagonalRestι {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) : offDiagonalRest f n ⟶ selfFibrePower f n :=
  closedImmersionComplementι (offDiagonalι f n)

/-- The structure morphism of the union of pairwise diagonals over `X`. -/
noncomputable def offDiagonalRestToBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) : offDiagonalRest f n ⟶ X :=
  offDiagonalRestι f n ≫ selfFibrePowerToBase f n

/-- `offDiagonalRestι` is the complement inclusion of the off-diagonal closed immersion. -/
theorem offDiagonalRestι_eq {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) :
    offDiagonalRestι f n = closedImmersionComplementι (offDiagonalι f n) :=
  rfl

/-- The structure morphism of the union of pairwise diagonals is étale. -/
instance instEtale_offDiagonalRestToBase {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) : Etale (offDiagonalRestToBase f n) :=
  sorry

/-- The clopen copairing `W ⨿ Rest ⟶ U^{×_X n}` of the off-diagonal locus with the union
of pairwise diagonals. -/
noncomputable def offDiagonalClopenCopairing {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) :
    binaryCoproduct (offDiagonal f n) (offDiagonalRest f n) ⟶ selfFibrePower f n :=
  coproductDesc (finTwoHom (offDiagonalι f n) (offDiagonalRestι f n))

/-- The clopen copairing is `coproductDesc` of the two inclusions into the fibre product. -/
theorem offDiagonalClopenCopairing_eq {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) :
    offDiagonalClopenCopairing f n =
      coproductDesc (finTwoHom (offDiagonalι f n) (offDiagonalRestι f n)) :=
  rfl

/-- The clopen copairing of `W` with the union of diagonals is an isomorphism onto the
fibre product. -/
instance instIsIso_offDiagonalClopenCopairing {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) : IsIso (offDiagonalClopenCopairing f n) :=
  sorry

/-- A map into the `n`-fold fibre product misses every pairwise diagonal. -/
def missesPairwiseDiagonals {T U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    {n : ℕ} (h : T ⟶ selfFibrePower f n) : Prop :=
  ∀ (i : Fin n) (j : Fin i.val) (V : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj V),
    missesClosedImage (pairwiseDiagonalι f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i)
      (h.app V t)

/-- Missing pairwise diagonals is the pointwise missing-closed-image condition on every
strictly ordered pair. -/
theorem missesPairwiseDiagonals_iff {T U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] {n : ℕ} (h : T ⟶ selfFibrePower f n) :
    missesPairwiseDiagonals f h ↔
      ∀ (i : Fin n) (j : Fin i.val) (V : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj V),
        missesClosedImage (pairwiseDiagonalι f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i)
          (h.app V t) :=
  Iff.rfl

/-- A map into the `n`-fold fibre product that misses every pairwise diagonal lifts to
the off-diagonal locus. -/
noncomputable def offDiagonalLift {T U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) (h : T ⟶ selfFibrePower f n) (h_miss : missesPairwiseDiagonals f h) :
    T ⟶ offDiagonal f n :=
  OpenSubspace.infFamilyLift n (pairwiseDiagonalComplementFamily f n) h fun i j =>
    closedImmersionComplementLift
      (pairwiseDiagonalι f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i) h fun V t =>
      h_miss i j V t

/-- The lift to the off-diagonal locus composes to the original map into the fibre
product. -/
theorem offDiagonalLift_comp {T U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) (h : T ⟶ selfFibrePower f n) (h_miss : missesPairwiseDiagonals f h) :
    offDiagonalLift f n h h_miss ≫ offDiagonalι f n = h :=
  sorry

/-- Permuting the factors of the fibre product preserves the off-diagonal locus. -/
theorem offDiagonalPerm_missesPairwiseDiagonals {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    missesPairwiseDiagonals f (offDiagonalι f n ≫ (selfFibrePowerPerm f n σ).hom) :=
  sorry

/-- The permutation automorphism of the off-diagonal locus induced by permuting the
factors of the ambient fibre product. The inverse is the same mediating morphism at
`σ⁻¹`. -/
noncomputable def offDiagonalPerm {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : Equiv.Perm (Fin n) →* Aut (offDiagonal f n) where
  toFun σ :=
    { hom :=
        offDiagonalLift f n (offDiagonalι f n ≫ (selfFibrePowerPerm f n σ).hom)
          (offDiagonalPerm_missesPairwiseDiagonals f n σ)
      inv :=
        offDiagonalLift f n (offDiagonalι f n ≫ (selfFibrePowerPerm f n σ⁻¹).hom)
          (offDiagonalPerm_missesPairwiseDiagonals f n σ⁻¹)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The permutation action on the off-diagonal locus lies over `X`. -/
theorem offDiagonalPerm_comp_toBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (offDiagonalPerm f n σ).hom ≫ offDiagonalToBase f n = offDiagonalToBase f n :=
  sorry

/-- The off-diagonal permutation action, with `S_n` lifted to the universe of `S`. -/
noncomputable def offDiagonalPermLift {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) :
    ULift.{u} (Equiv.Perm (Fin n)) →* Aut (offDiagonal f n) :=
  (offDiagonalPerm f n).comp
    (MulEquiv.ulift (α := Equiv.Perm (Fin n))).toMonoidHom

/-- `offDiagonalPermLift` evaluates as `offDiagonalPerm` on the underlying permutation. -/
theorem offDiagonalPermLift_apply {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    offDiagonalPermLift f n σ = offDiagonalPerm f n σ.down :=
  rfl

/-- Automorphisms coming from the permutation action on the off-diagonal locus are
étale. -/
instance instEtale_offDiagonalPerm {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Etale ((offDiagonalPerm f n σ).hom) :=
  sorry

/-- For `n = 1` there are no pairwise diagonals, and `W_0` is isomorphic to `U`. -/
noncomputable def offDiagonal_one {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] :
    offDiagonal f 1 ≅ U where
  hom := offDiagonalι f 1 ≫ pullback.snd (selfFibrePowerToBase f 0) f
  inv := offDiagonalLift f 1 (pullback.lift f (𝟙 U) sorry) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Abelian étale sheaves on an algebraic space form a preadditive category. -/
instance smallEtaleTopology_preadditive_addCommGrpCat (X : AlgebraicSpace S) :
    Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Composite étale restriction functors are continuous. -/
instance etaleRestriction_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    (etaleRestriction f ⋙ etaleRestriction g).IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology Z) :=
  Functor.isContinuous_comp (etaleRestriction f) (etaleRestriction g)
    (smallEtaleTopology X) (smallEtaleTopology Y) (smallEtaleTopology Z)

/-- Equal étale morphisms induce equal restriction functors on small étale sites. -/
theorem etaleRestriction_eq_of_eq {X Y : AlgebraicSpace S} {f g : X ⟶ Y}
    [Etale f] [Etale g] (h : f = g) : etaleRestriction f = etaleRestriction g :=
  sorry

/-- Identification `(ρ σ)^* (F|_W) ≅ F|_W` coming from the permutation lying over `X`. -/
noncomputable def offDiagonalRestrictionPastingIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1} ⋙
        etaleRestrictionSheaf (offDiagonalPerm f n σ).hom AddCommGrpCat.{u + 1} ≅
      etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp (etaleRestriction (offDiagonalPerm f n σ).hom)
      (etaleRestriction (offDiagonalToBase f n)) AddCommGrpCat.{u + 1}
      (smallEtaleTopology (offDiagonal f n)) (smallEtaleTopology (offDiagonal f n))
      (smallEtaleTopology X) ≪≫
    Functor.sheafPushforwardContinuousIso
      (eqToIso
        (etaleRestriction_comp (offDiagonalPerm f n σ).hom (offDiagonalToBase f n)).symm)
      AddCommGrpCat.{u + 1} (smallEtaleTopology (offDiagonal f n)) (smallEtaleTopology X) ≪≫
    Functor.sheafPushforwardContinuousIso
      (eqToIso (etaleRestriction_eq_of_eq (offDiagonalPerm_comp_toBase f n σ)))
      AddCommGrpCat.{u + 1} (smallEtaleTopology (offDiagonal f n)) (smallEtaleTopology X)

/-- The `Equiv.Perm (Fin n)`-action on `F(W)` by pullback along the off-diagonal
permutation automorphisms, for an abelian sheaf `F` on `X_étale`. -/
noncomputable def offDiagonalSectionsAction {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    Equiv.Perm (Fin n) →* Aut
      ((globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F)) where
  toFun σ :=
    { hom :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (offDiagonalPerm f n σ).hom ≫
                (etaleRestrictionSheaf (offDiagonalPerm f n σ).hom
                    AddCommGrpCat.{u + 1}).map s ≫
                  (offDiagonalRestrictionPastingIso f n σ).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      inv :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (offDiagonalPerm f n σ⁻¹).hom ≫
                (etaleRestrictionSheaf (offDiagonalPerm f n σ⁻¹).hom
                    AddCommGrpCat.{u + 1}).map s ≫
                  (offDiagonalRestrictionPastingIso f n σ⁻¹).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The additive subgroup of `S_n`-anti-invariants in an abelian group equipped with a
permutation action. -/
def permAntiInvariantsAddSubgroup {n : ℕ} {A : AddCommGrpCat.{u + 1}}
    (σ : Equiv.Perm (Fin n) →* Aut A) : AddSubgroup A where
  carrier :=
    { a | ∀ g : Equiv.Perm (Fin n),
        (σ g).hom a = ((Equiv.Perm.sign g : ℤˣ) : ℤ) • a }
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- The group of `S_n`-anti-invariant elements of an abelian group with permutation
action. -/
noncomputable def permAntiInvariants {n : ℕ} {A : AddCommGrpCat.{u + 1}}
    (σ : Equiv.Perm (Fin n) →* Aut A) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (permAntiInvariantsAddSubgroup σ)

/-- The inclusion of `S_n`-anti-invariants into the ambient abelian group. -/
noncomputable def permAntiInvariants_ι {n : ℕ} {A : AddCommGrpCat.{u + 1}}
    (σ : Equiv.Perm (Fin n) →* Aut A) : permAntiInvariants σ ⟶ A :=
  AddCommGrpCat.ofHom (permAntiInvariantsAddSubgroup σ).subtype

/-- Membership in `permAntiInvariants` is the signed transformation law for every
permutation. -/
theorem mem_permAntiInvariants {n : ℕ} {A : AddCommGrpCat.{u + 1}}
    (σ : Equiv.Perm (Fin n) →* Aut A) (a : A) :
    a ∈ permAntiInvariantsAddSubgroup σ ↔
      ∀ g : Equiv.Perm (Fin n),
        (σ g).hom a = ((Equiv.Perm.sign g : ℤˣ) : ℤ) • a :=
  Iff.rfl

/-- An equivariant morphism of ambient abelian groups induces a morphism of
anti-invariant subgroups. -/
noncomputable def permAntiInvariants_map {n : ℕ} {A B : AddCommGrpCat.{u + 1}}
    {σA : Equiv.Perm (Fin n) →* Aut A} {σB : Equiv.Perm (Fin n) →* Aut B} (ψ : A ⟶ B)
    (h_equivariant : ∀ g : Equiv.Perm (Fin n), (σA g).hom ≫ ψ = ψ ≫ (σB g).hom) :
    permAntiInvariants σA ⟶ permAntiInvariants σB :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ ⟨ψ (a : A), sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The inclusion of anti-invariants is the subtype inclusion of the signed-invariants
subgroup. -/
theorem permAntiInvariants_ι_eq {n : ℕ} {A : AddCommGrpCat.{u + 1}}
    (σ : Equiv.Perm (Fin n) →* Aut A) :
    permAntiInvariants_ι σ = AddCommGrpCat.ofHom (permAntiInvariantsAddSubgroup σ).subtype :=
  rfl

/-- The anti-invariant map intertwines the subtype inclusions of the signed-invariants
subgroups. -/
theorem permAntiInvariants_map_ι {n : ℕ} {A B : AddCommGrpCat.{u + 1}}
    {σA : Equiv.Perm (Fin n) →* Aut A} {σB : Equiv.Perm (Fin n) →* Aut B} (ψ : A ⟶ B)
    (h_equivariant : ∀ g : Equiv.Perm (Fin n), (σA g).hom ≫ ψ = ψ ≫ (σB g).hom) :
    permAntiInvariants_ι σA ≫ ψ =
      permAntiInvariants_map ψ h_equivariant ≫ permAntiInvariants_ι σB :=
  sorry

/-- The map on `F(W)` induced by a morphism of abelian sheaves on `X_étale`. -/
noncomputable def offDiagonalSectionsMap {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) ⟶
      (globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj G) :=
  (globalSections (offDiagonal f n)).map
    ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).map φ)

/-- `offDiagonalSectionsMap` is global sections of étale restriction of `φ`. -/
theorem offDiagonalSectionsMap_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    offDiagonalSectionsMap f n φ =
      (globalSections (offDiagonal f n)).map
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).map φ) :=
  rfl

/-- Restriction of abelian sheaves is equivariant for the off-diagonal permutation
action on global sections. -/
theorem offDiagonalSectionsMap_equivariant {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    ∀ g : Equiv.Perm (Fin n),
      (offDiagonalSectionsAction f n F g).hom ≫ offDiagonalSectionsMap f n φ =
        offDiagonalSectionsMap f n φ ≫ (offDiagonalSectionsAction f n G g).hom :=
  sorry

/-- The map on `S_n`-anti-invariants of `F(W)` induced by a morphism of abelian
sheaves. -/
noncomputable def offDiagonalAntiInvariantsMap {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    permAntiInvariants (offDiagonalSectionsAction f n F) ⟶
      permAntiInvariants (offDiagonalSectionsAction f n G) :=
  permAntiInvariants_map (offDiagonalSectionsMap f n φ)
    (offDiagonalSectionsMap_equivariant f n φ)

/-- `offDiagonalAntiInvariantsMap` is the equivariant `permAntiInvariants_map` of
`offDiagonalSectionsMap`. -/
theorem offDiagonalAntiInvariantsMap_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    offDiagonalAntiInvariantsMap f n φ =
      permAntiInvariants_map (offDiagonalSectionsMap f n φ)
        (offDiagonalSectionsMap_equivariant f n φ) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
