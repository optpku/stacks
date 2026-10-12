/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham
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
      Finsupp.single (generatorMap b p x) (b c) := sorry

/-- A commuting ring square makes the free basic-form map preserve evaluation relations. -/
theorem relations_map (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ) :
    relations A B p ≤ (relations A' B' p).comap (freeMap b p) := sorry

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
    formMap a b h p (r • x) = a r • formMap a b h p x := sorry

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
      basic A' B' p (b b₀) (fun i ↦ b (bs i)) := sorry

/-- The scalar-restricted term map acts entrywise on basic forms. -/
theorem map_basic (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (p : ℕ) (b₀ : B) (bs : Fin p → B) :
    map a b h p (basic A B p b₀ bs) =
      basic A' B' p (b b₀) (fun i ↦ b (bs i)) := sorry

/-- Maps induced by commuting ring squares intertwine the de Rham differentials. -/
theorem map_d (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (p : ℕ) (x : Form A B p) :
    map a b h (p + 1) (d A B p x) = d A' B' p (map a b h p x) := sorry

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
    d f p ≫ d f (p + 1) = 0 := sorry

/-- The algebraic de Rham complex attached to a morphism of commutative rings. -/
@[stacks 0FKF]
noncomputable def complex (f : A ⟶ B) : CochainComplex (ModuleCat.{u} A) ℕ :=
  letI := f.hom.toAlgebra
  KaehlerDifferential.DeRham.complex A B

/-- The ring-homomorphism equality supplied by a commutative categorical square. -/
theorem hom_comm {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) :
    f'.hom.comp a.hom = b.hom.comp f.hom := sorry

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
      basic f' p (b b₀) (fun i ↦ b (bs i)) := sorry

/-- The categorical term map acts entrywise on basic forms. -/
theorem mapApp_basic {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) (b₀ : B) (bs : Fin p → B) :
    mapApp sq p (basic f p b₀ bs) =
      basic f' p (b b₀) (fun i ↦ b (bs i)) := sorry

/-- The categorical square map commutes with consecutive de Rham differentials. -/
theorem mapApp_d {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (p : ℕ) :
    d f p ≫ mapApp sq (p + 1) =
      mapApp sq p ≫ (ModuleCat.restrictScalars a.hom).map (d f' p) := sorry

/-- Restriction of scalars on cochain complexes along a ring morphism. -/
abbrev restriction (a : A ⟶ A') :=
  (ModuleCat.restrictScalars a.hom).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The degreewise square maps satisfy the full complex commutativity relation. -/
theorem mapApp_comm {a : A ⟶ A'} {f : A ⟶ B} {f' : A' ⟶ B'} {b : B ⟶ B'}
    (sq : CommSq a f f' b) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    mapApp sq i ≫ ((restriction a).obj (complex f')).d i j =
      (complex f).d i j ≫ mapApp sq j := sorry

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
    (map sq).f p = mapApp sq p := sorry

/-- The commutative square with identity horizontal maps and vertical map `f`. -/
@[stacks 0FKF "identity square for algebraic de Rham maps"]
theorem idSquare (f : A ⟶ B) : CommSq (𝟙 A) f f (𝟙 B) := sorry

/-- The form map for an identity square is pointwise the identity. -/
theorem formMapApp_id_apply (f : A ⟶ B) (p : ℕ) (x : form f p) :
    formMapApp (idSquare f) p x = x := sorry

/-- The term map for an identity square is pointwise the identity. -/
theorem mapApp_id_apply (f : A ⟶ B) (p : ℕ) (x : term f p) :
    mapApp (idSquare f) p x = x := sorry

/-- Form maps are pointwise compatible with horizontal composition of squares. -/
theorem formMapApp_comp_apply {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b')
    (p : ℕ) (x : form f p) :
    formMapApp sq' p (formMapApp sq p x) =
      formMapApp (CommSq.horiz_comp sq sq') p x := sorry

/-- Term maps are pointwise compatible with horizontal composition of squares. -/
theorem mapApp_comp_apply {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b')
    (p : ℕ) (x : term f p) :
    mapApp sq' p (mapApp sq p x) =
      mapApp (CommSq.horiz_comp sq sq') p x := sorry

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
      (idIso B).hom.app (DeRham.form f p) := sorry

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
        DeRham.formMapApp (CommSq.horiz_comp sq sq') p := sorry

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
      (ModuleCat.restrictScalarsId A).inv.app (DeRham.term f p) := sorry

/-- Algebraic de Rham maps preserve horizontal composition after scalar-restriction coherence. -/
@[stacks 0FKF "composition law for algebraic de Rham maps"]
theorem mapApp_comp
    {a : A ⟶ A'} {a' : A' ⟶ A''}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    {b : B ⟶ B'} {b' : B' ⟶ B''}
    (sq : CommSq a f f' b) (sq' : CommSq a' f' f'' b') (p : ℕ) :
    DeRham.mapApp sq p ≫ (ModuleCat.restrictScalars a.hom).map (DeRham.mapApp sq' p) ≫
        (ModuleCat.restrictScalarsComp a.hom a'.hom).inv.app (DeRham.term f'' p) =
      DeRham.mapApp (CommSq.horiz_comp sq sq') p := sorry

/-- The complex map of an identity square is the canonical identity-restriction isomorphism. -/
@[simp, stacks 0FKF "identity law for algebraic de Rham complexes"]
theorem map_id (f : A ⟶ B) :
    DeRham.map (DeRham.idSquare f) =
      (idIso A).hom.app (DeRham.complex f) := sorry

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
      DeRham.map (CommSq.horiz_comp sq sq') := sorry

end Restriction

end CommRingCat.DeRham
