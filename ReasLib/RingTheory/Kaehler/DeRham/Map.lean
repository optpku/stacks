/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham
public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.CommSq

/-!
# Functoriality of the algebraic de Rham complex

A commutative square of commutative rings acts semilinearly on relative differential forms along
the lower ring map.  After restricting scalars, the same explicit function is semilinear along the
upper ring map and therefore gives a map of de Rham complexes.

The `CommRingCat.DeRham` namespace packages these two coefficient levels so consumers only pass a
ring morphism or a `CommSq`.  The morphism-dependent algebra instances are confined to this owner
boundary.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u

namespace KaehlerDifferential.DeRham

variable {A A' B B' : Type u}
variable [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
variable [Algebra A B] [Algebra A' B']

/-- The image of an index for a basic form under a ring homomorphism. -/
def generatorMap (b : B →+* B') (p : ℕ) : Generator B p → Generator B' p :=
  fun x ↦ (b x.1, fun i ↦ b (x.2 i))

/-- The semilinear map on free basic-form modules induced by a map of total rings. -/
def freeMap (b : B →+* B') (p : ℕ) : Free B p →ₛₗ[b] Free B' p :=
  (Finsupp.lmapDomain B' B' (generatorMap b p)).comp
    (Finsupp.mapRange.linearMap b.toSemilinearMap)

/-- The free basic-form map applies the total-ring map to coefficients and entries. -/
theorem freeMap_single (b : B →+* B') (p : ℕ) (x : Generator B p) (c : B) :
    freeMap b p (Finsupp.single x c) =
      Finsupp.single (generatorMap b p x) (b c) := by
  simp [freeMap]

private theorem freeMap_id (p : ℕ) (x : Free B p) :
    freeMap (RingHom.id B) p x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single x c => simp [freeMap_single, generatorMap]

private theorem freeMap_comp {C : Type u} [CommRing C]
    (b : B →+* B') (b' : B' →+* C) (p : ℕ) (x : Free B p) :
    freeMap b' p (freeMap b p x) = freeMap (b'.comp b) p x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single x c => simp [freeMap_single, generatorMap]

/-- A commuting ring square makes the free basic-form map preserve evaluation relations. -/
theorem relations_map (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ) :
    relations A B p ≤ (relations A' B' p).comap (freeMap b p) := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  letI := ((algebraMap A' B').comp a).toAlgebra
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' h
  letI : SMulCommClass A' B B' := SMulCommClass.of_commMonoid A' B B'
  let κ := KaehlerDifferential.map A A' B B'
  obtain ⟨F, hF⟩ : ∃ F : exteriorPower.form B Ω[B⁄A] p →ₛₗ[b]
      exteriorPower.form B' Ω[B'⁄A'] p,
      ∀ x : Generator B p,
        F (DifferentialOperator.DeRham.basicForm (D A B) p x.1 x.2) =
          DifferentialOperator.DeRham.basicForm (D A' B') p (b x.1) (fun i ↦ b (x.2 i)) := by
    rcases p with _ | _ | p
    · change ∃ F : B →ₛₗ[b] B', ∀ x : Generator B 0, F (x.1 * 1) = b x.1 * 1
      refine ⟨b.toSemilinearMap, ?_⟩
      intro x
      simp
    · change ∃ F : Ω[B⁄A] →ₛₗ[b] Ω[B'⁄A'], ∀ x : Generator B 1,
        F (x.1 • D A B (x.2 0)) = b x.1 • D A' B' (b (x.2 0))
      refine ⟨{ toFun := κ, map_add' := κ.map_add, map_smul' := ?_ }, ?_⟩
      · intro c x
        rw [κ.map_smul, ← IsScalarTower.algebraMap_smul B' c (κ x)]
        rfl
      · intro x
        change κ (x.1 • D A B (x.2 0)) = b x.1 • D A' B' (b (x.2 0))
        rw [κ.map_smul, ← IsScalarTower.algebraMap_smul B' x.1]
        exact congrArg (fun ω : Ω[B'⁄A'] ↦ b x.1 • ω)
          (KaehlerDifferential.map_D A A' B B' (x.2 0))
    · let F₀ := exteriorPower.restrictScalarsMap (R := B) (S := B') (p + 2) κ
      refine ⟨{ toFun := F₀, map_add' := F₀.map_add, map_smul' := F₀.map_smul }, ?_⟩
      intro x
      change F₀ (x.1 • exteriorPower.ιMulti B (p + 2) (fun i ↦ D A B (x.2 i))) =
        b x.1 • exteriorPower.ιMulti B' (p + 2) (fun i ↦ D A' B' (b (x.2 i)))
      rw [F₀.map_smul]
      change b x.1 • (show ⋀[B']^(p + 2) Ω[B'⁄A'] from
        F₀ (exteriorPower.ιMulti B (p + 2) (fun i ↦ D A B (x.2 i)))) = _
      congr 1
      have hι : F₀ (exteriorPower.ιMulti B (p + 2) (fun i ↦ D A B (x.2 i))) =
          (exteriorPower.ιMulti B' (p + 2) (fun i ↦ κ (D A B (x.2 i))) :
            RestrictScalars B B' (⋀[B']^(p + 2) Ω[B'⁄A'])) :=
        @exteriorPower.alternatingMapLinearEquiv_apply_ιMulti B _ (p + 2) Ω[B⁄A]
          (RestrictScalars B B' (⋀[B']^(p + 2) Ω[B'⁄A'])) _ _ _
          (RestrictScalars.module B B' (⋀[B']^(p + 2) Ω[B'⁄A'])) _ _
      have hκ : (fun i : Fin (p + 2) ↦ κ (D A B (x.2 i))) =
          (fun i ↦ D A' B' (b (x.2 i))) := by
        funext i
        exact KaehlerDifferential.map_D A A' B B' (x.2 i)
      exact hι.trans (congrArg (fun m ↦ (exteriorPower.ιMulti B' (p + 2) m :
        RestrictScalars B B' (⋀[B']^(p + 2) Ω[B'⁄A']))) hκ)
  let E := Finsupp.linearCombination B fun x : Generator B p ↦
    DifferentialOperator.DeRham.basicForm (D A B) p x.1 x.2
  let E' := Finsupp.linearCombination B' fun x : Generator B' p ↦
    DifferentialOperator.DeRham.basicForm (D A' B') p x.1 x.2
  have heval (y : Free B p) : E' (freeMap b p y) = F (E y) := by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y z hy hz => simp [map_add, hy, hz]
    | single x c => simp [E, E', freeMap_single, generatorMap, hF]
  intro y hy
  change E y = 0 at hy
  change E' (freeMap b p y) = 0
  rw [heval, hy, map_zero]


/-- The map on relative differential forms, semilinear along the total-ring map. -/
@[stacks 0FKF]
def formMap (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ) :
    Form A B p →ₛₗ[b] Form A' B' p :=
  (relations A B p).mapQ (relations A' B' p) (freeMap b p) (relations_map a b h p)

/-- The form map is semilinear along the upper map after restricting scalars. -/
theorem formMap_smul (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ)
    (r : A) (x : Form A B p) :
    formMap a b h p (r • x) = a r • formMap a b h p x := by
  have hr : algebraMap A' B' (a r) = b (algebraMap A B r) := RingHom.congr_fun h r
  rw [← IsScalarTower.algebraMap_smul B r x, map_smulₛₗ,
    ← hr, IsScalarTower.algebraMap_smul]

/-- The map on scalar-restricted de Rham terms, semilinear along the base-ring map. -/
@[stacks 0FKF]
def map (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ) :
    Form A B p →ₛₗ[a] Form A' B' p where
  toFun := formMap a b h p
  map_add' := (formMap a b h p).map_add
  map_smul' := formMap_smul a b h p

/-- The induced form map applies the lower ring map to every entry of a basic form. -/
theorem formMap_basic (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (p : ℕ) (b₀ : B) (bs : Fin p → B) :
    formMap a b h p (basic A B p b₀ bs) =
      basic A' B' p (b b₀) (fun i ↦ b (bs i)) := by
  change Submodule.Quotient.mk (freeMap b p (Finsupp.single (b₀, bs) 1)) = _
  rw [freeMap_single, map_one]
  rfl

/-- The scalar-restricted term map acts entrywise on basic forms. -/
theorem map_basic (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (p : ℕ) (b₀ : B) (bs : Fin p → B) :
    map a b h p (basic A B p b₀ bs) =
      basic A' B' p (b b₀) (fun i ↦ b (bs i)) :=
  formMap_basic a b h p b₀ bs

private theorem quotient_single (p : ℕ) (x : Generator B p) (c : B) :
    (relations A B p).mkQ (Finsupp.single x c) = basic A B p (c * x.1) x.2 := by
  apply (Submodule.Quotient.eq _).mpr
  change (Finsupp.linearCombination B fun x : Generator B p ↦
    DifferentialOperator.DeRham.basicForm (KaehlerDifferential.D A B) p x.1 x.2)
    (Finsupp.single x c - Finsupp.single (c * x.1, x.2) 1) = 0
  simp [DifferentialOperator.DeRham.basicForm, mul_smul]

/-- Maps induced by commuting ring squares intertwine the de Rham differentials. -/
theorem map_d (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (p : ℕ) (x : Form A B p) :
    map a b h (p + 1) (d A B p x) = d A' B' p (map a b h p x) := by
  let δ : Form A B p →+ Form A B (p + 1) := (d A B p).hom.toAddMonoidHom
  let δ' : Form A' B' p →+ Form A' B' (p + 1) := (d A' B' p).hom.toAddMonoidHom
  change map a b h (p + 1) (δ x) = δ' (map a b h p x)
  refine Submodule.Quotient.induction_on _ x fun y ↦ ?_
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y z hy hz => simp [Submodule.Quotient.mk_add, map_add, hy, hz]
  | single y c =>
      change map a b h (p + 1) (d A B p ((relations A B p).mkQ
        (Finsupp.single y c))) = d A' B' p (map a b h p
          ((relations A B p).mkQ (Finsupp.single y c)))
      rw [quotient_single]
      simp only [d_basic, exact, map_basic, map_one]
      congr 1
      funext i
      cases i using Fin.cases <;> rfl

end KaehlerDifferential.DeRham

namespace CommRingCat.DeRham

variable {A A' A'' B B' B'' : CommRingCat.{u}}

/-- Relative differential `p`-forms of a morphism of commutative rings, as a module over its
target.  The algebra structure determined by the morphism is installed only at this owner. -/
@[stacks 0FKF]
noncomputable def form (f : A ⟶ B) (p : ℕ) : ModuleCat.{u} B :=
  letI := f.hom.toAlgebra
  KaehlerDifferential.DeRham.form A B p

/-- The scalar-restricted degree-`p` term of the de Rham complex of a ring morphism. -/
@[stacks 0FKF]
noncomputable def term (f : A ⟶ B) (p : ℕ) : ModuleCat.{u} A :=
  letI := f.hom.toAlgebra
  KaehlerDifferential.DeRham.term A B p

/-- A basic relative differential form in the categorical presentation. -/
noncomputable def basic (f : A ⟶ B) (p : ℕ) (b₀ : B) (bs : Fin p → B) : form f p :=
  letI := f.hom.toAlgebra
  KaehlerDifferential.DeRham.basic A B p b₀ bs

/-- The degree-raising differential on scalar-restricted categorical de Rham terms. -/
@[stacks 0FKF]
noncomputable def d (f : A ⟶ B) (p : ℕ) : term f p ⟶ term f (p + 1) :=
  letI := f.hom.toAlgebra
  KaehlerDifferential.DeRham.d A B p

/-- Consecutive categorical de Rham differentials compose to zero. -/
theorem d_sq (f : A ⟶ B) (p : ℕ) :
    d f p ≫ d f (p + 1) = 0 := by
  letI := f.hom.toAlgebra
  exact KaehlerDifferential.DeRham.d_sq A B p

/-- The algebraic de Rham complex attached to a morphism of commutative rings. -/
@[stacks 0FKF]
noncomputable def complex (f : A ⟶ B) : CochainComplex (ModuleCat.{u} A) ℕ :=
  letI := f.hom.toAlgebra
  KaehlerDifferential.DeRham.complex A B

/-- The ring-homomorphism equality supplied by a commutative categorical square. -/
theorem hom_comm {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) :
    f'.hom.comp a.hom = b.hom.comp f.hom :=
  congrArg CommRingCat.Hom.hom sq.w

/-- The degree-`p` map on form modules induced by a commutative square of rings. -/
@[stacks 0FKF]
noncomputable def formMapApp {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) :
    form f p ⟶ (ModuleCat.restrictScalars b.hom).obj (form f' p) :=
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  ModuleCat.semilinearMapAddEquiv b.hom (form f p) (form f' p)
    (KaehlerDifferential.DeRham.formMap a.hom b.hom (hom_comm sq) p)

/-- The degree-`p` map on scalar-restricted terms induced by a commutative square of rings. -/
@[stacks 0FKF]
noncomputable def mapApp {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) :
    term f p ⟶ (ModuleCat.restrictScalars a.hom).obj (term f' p) :=
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  ModuleCat.semilinearMapAddEquiv a.hom (term f p) (term f' p)
    (KaehlerDifferential.DeRham.map a.hom b.hom (hom_comm sq) p)

/-- The categorical form map acts entrywise on basic forms. -/
theorem formMapApp_basic {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) (b₀ : B) (bs : Fin p → B) :
    formMapApp sq p (basic f p b₀ bs) =
      basic f' p (b b₀) (fun i ↦ b (bs i)) := by
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  exact KaehlerDifferential.DeRham.formMap_basic a.hom b.hom (hom_comm sq) p b₀ bs

/-- The categorical term map acts entrywise on basic forms. -/
theorem mapApp_basic {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) (b₀ : B) (bs : Fin p → B) :
    mapApp sq p (basic f p b₀ bs) =
      basic f' p (b b₀) (fun i ↦ b (bs i)) :=
  formMapApp_basic sq p b₀ bs

/-- The categorical square map commutes with consecutive de Rham differentials. -/
theorem mapApp_d {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) :
    d f p ≫ mapApp sq (p + 1) =
      mapApp sq p ≫ (ModuleCat.restrictScalars a.hom).map (d f' p) := by
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  ext x
  exact KaehlerDifferential.DeRham.map_d a.hom b.hom (hom_comm sq) p x

/-- Restriction of scalars on cochain complexes along a ring morphism. -/
abbrev restriction (a : A ⟶ A') :=
  (ModuleCat.restrictScalars a.hom).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The degreewise square maps satisfy the full complex commutativity relation. -/
theorem mapApp_comm {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    mapApp sq i ≫ ((restriction a).obj (complex f')).d i j =
      (complex f).d i j ≫ mapApp sq j := by
  have h : i + 1 = j := hij
  subst j
  change mapApp sq i ≫ (ModuleCat.restrictScalars a.hom).map
      ((complex f').d i (i + 1)) = (complex f).d i (i + 1) ≫ mapApp sq (i + 1)
  simpa only [complex, KaehlerDifferential.DeRham.complex, CochainComplex.of_d, d, term]
    using (mapApp_d sq i).symm

/-- The morphism of de Rham complexes induced by a commutative square of rings. -/
@[stacks 0FKF]
noncomputable def map {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) :
    complex f ⟶ (restriction a).obj (complex f') where
  f p := mapApp sq p
  comm' i j hij := mapApp_comm sq i j hij

/-- The degree-`p` component of the algebraic de Rham map is the corresponding term map. -/
@[simp, stacks 0FKF "degreewise component of algebraic de Rham maps"]
theorem map_f {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) :
    (map sq).f p = mapApp sq p := rfl

/-- The commutative square with identity horizontal maps and vertical map `f`. -/
@[stacks 0FKF "identity square for algebraic de Rham maps"]
theorem idSquare (f : A ⟶ B) : CommSq (𝟙 A) f f (𝟙 B) := ⟨by simp⟩

/-- The form map for an identity square is pointwise the identity. -/
theorem formMapApp_id_apply (f : A ⟶ B) (p : ℕ) (x : form f p) :
    formMapApp (idSquare f) p x = x := by
  letI := f.hom.toAlgebra
  refine Submodule.Quotient.induction_on _ x fun y ↦ ?_
  change Submodule.Quotient.mk
    (KaehlerDifferential.DeRham.freeMap (RingHom.id B) p y) = Submodule.Quotient.mk y
  rw [KaehlerDifferential.DeRham.freeMap_id]

/-- The term map for an identity square is pointwise the identity. -/
theorem mapApp_id_apply (f : A ⟶ B) (p : ℕ) (x : term f p) :
    mapApp (idSquare f) p x = x :=
  formMapApp_id_apply f p x

/-- Form maps are pointwise compatible with horizontal composition of squares. -/
theorem formMapApp_comp_apply {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b')
    (p : ℕ) (x : form f p) :
    formMapApp sq' p (formMapApp sq p x) =
      formMapApp (CommSq.horiz_comp sq sq') p x := by
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  letI := f''.hom.toAlgebra
  refine Submodule.Quotient.induction_on _ x fun y ↦ ?_
  change Submodule.Quotient.mk (KaehlerDifferential.DeRham.freeMap b'.hom p
      (KaehlerDifferential.DeRham.freeMap b.hom p y)) =
    Submodule.Quotient.mk (KaehlerDifferential.DeRham.freeMap (b'.hom.comp b.hom) p y)
  rw [KaehlerDifferential.DeRham.freeMap_comp]

/-- Term maps are pointwise compatible with horizontal composition of squares. -/
theorem mapApp_comp_apply {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b')
    (p : ℕ) (x : term f p) :
    mapApp sq' p (mapApp sq p x) =
      mapApp (CommSq.horiz_comp sq sq') p x :=
  formMapApp_comp_apply sq sq' p x

namespace FormRestriction

/-- The identity-restriction comparison for relative form modules. -/
@[stacks 0FKF "identity restriction for algebraic de Rham form maps"]
noncomputable def idIso (B : CommRingCat.{u}) :
    (𝟭 (ModuleCat.{u} B) : ModuleCat.{u} B ⥤ ModuleCat.{u} B) ≅
      ModuleCat.restrictScalars (RingHom.id B) :=
  (ModuleCat.restrictScalarsId B).symm

/-- The comparison from two successive restrictions of relative form modules to restriction along
their composite. -/
@[stacks 0FKF "composition restriction for algebraic de Rham form maps"]
noncomputable def compIso (b : B ⟶ B') (b' : B' ⟶ B'') :
    ModuleCat.restrictScalars b'.hom ⋙ ModuleCat.restrictScalars b.hom ≅
      ModuleCat.restrictScalars (b ≫ b').hom :=
  (ModuleCat.restrictScalarsComp b.hom b'.hom).symm

/-- The degreewise form map of an identity square is the canonical identity-restriction morphism. -/
@[simp, stacks 0FKF "identity law for algebraic de Rham form maps"]
theorem mapApp_id (f : A ⟶ B) (p : ℕ) :
    DeRham.formMapApp (DeRham.idSquare f) p =
      (idIso B).hom.app (DeRham.form f p) := by
  ext x
  exact DeRham.formMapApp_id_apply f p x

/-- Degreewise form maps preserve horizontal composition after scalar-restriction coherence. -/
@[stacks 0FKF "composition law for algebraic de Rham form maps"]
theorem mapApp_comp
    {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b') (p : ℕ) :
    DeRham.formMapApp sq p ≫ (ModuleCat.restrictScalars b.hom).map
        (DeRham.formMapApp sq' p) ≫
      (compIso b b').hom.app (DeRham.form f'' p) =
        DeRham.formMapApp (CommSq.horiz_comp sq sq') p := by
  ext x
  exact DeRham.formMapApp_comp_apply sq sq' p x

end FormRestriction

namespace Restriction

/-- The identity-restriction comparison for algebraic de Rham complexes. -/
@[stacks 0FKF "identity restriction for algebraic de Rham complexes"]
noncomputable def idIso (A : CommRingCat.{u}) :
    (𝟭 (CochainComplex (ModuleCat.{u} A) ℕ)) ≅ DeRham.restriction (𝟙 A) :=
  (Functor.mapHomologicalComplexIdIso (ModuleCat A) (ComplexShape.up ℕ)).symm ≪≫
    (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId A) (ComplexShape.up ℕ)).symm

/-- The comparison from two successive scalar restrictions to restriction along their composite. -/
@[stacks 0FKF "composition restriction for algebraic de Rham complexes"]
noncomputable def compIso (a : A ⟶ A') (a' : A' ⟶ A'') :
    DeRham.restriction a' ⋙ DeRham.restriction a ≅
      DeRham.restriction (a ≫ a') :=
  Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp a.hom a'.hom).symm (ComplexShape.up ℕ)

/-- The degreewise map of an identity square is the canonical identity-restriction morphism. -/
@[simp, stacks 0FKF "identity law for algebraic de Rham maps"]
theorem mapApp_id (f : A ⟶ B) (p : ℕ) :
    DeRham.mapApp (DeRham.idSquare f) p =
      (ModuleCat.restrictScalarsId A).inv.app (DeRham.term f p) := by
  ext x
  exact DeRham.mapApp_id_apply f p x

/-- Algebraic de Rham maps preserve horizontal composition after scalar-restriction coherence. -/
@[stacks 0FKF "composition law for algebraic de Rham maps"]
theorem mapApp_comp
    {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b') (p : ℕ) :
    DeRham.mapApp sq p ≫ (ModuleCat.restrictScalars a.hom).map (DeRham.mapApp sq' p) ≫
        (ModuleCat.restrictScalarsComp a.hom a'.hom).inv.app (DeRham.term f'' p) =
      DeRham.mapApp (CommSq.horiz_comp sq sq') p := by
  ext x
  exact DeRham.mapApp_comp_apply sq sq' p x

/-- The complex map of an identity square is the canonical identity-restriction isomorphism. -/
@[simp, stacks 0FKF "identity law for algebraic de Rham complexes"]
theorem map_id (f : A ⟶ B) :
    DeRham.map (DeRham.idSquare f) =
      (idIso A).hom.app (DeRham.complex f) := by
  apply HomologicalComplex.Hom.ext
  funext p
  exact mapApp_id f p

/-- Algebraic de Rham complex maps preserve horizontal composition after scalar-restriction
coherence. -/
@[stacks 0FKF "composition law for algebraic de Rham complexes"]
theorem map_comp
    {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b') :
    DeRham.map sq ≫ (DeRham.restriction a).map (DeRham.map sq') ≫
        (compIso a a').hom.app (DeRham.complex f'') =
      DeRham.map (CommSq.horiz_comp sq sq') := by
  apply HomologicalComplex.Hom.ext
  funext p
  exact mapApp_comp sq sq' p

end Restriction

end CommRingCat.DeRham
