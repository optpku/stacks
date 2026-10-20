module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Wedge
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Equation Gysin morphisms for relative differential forms

This file gives the quotient presentation of relative forms on the closed subscheme cut out by
an ordered finite family of global equations, and descends the local-cohomology class of the
corresponding ordered differential wedge through that presentation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite TopologicalSpace
open scoped MonoidalCategory

noncomputable section

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Gysin

variable {X S : Scheme.{u}}

/--
Relative `p`-forms for a scheme morphism, kept in the ambient scheme's module category.
-/
abbrev relativeForm (q : X ⟶ S) (p : ℕ) : X.Modules :=
  (Scheme.Modules.fromRingedSpace X).obj
    (RingedSpace.DeRham.form.{u} q.toLRSHom.toShHom p)

/--
The canonical closed subscheme of `X` cut out by the ordered family `fs`.
-/
noncomputable def zeroSubscheme {c : ℕ} (fs : Fin c → Γ(X, ⊤)) : Scheme.{u} :=
  (IdealSheafData.ofIdealTop (Ideal.span (Set.range fs))).subscheme

/--
The ordered relative differential form `d(fs 0) ∧ ⋯ ∧ d(fs (c - 1))`, represented
as the basic relative `c`-form with coefficient one.
-/
noncomputable def equationForm (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) :
    (relativeForm q c).val.obj (op ⊤) :=
  SheafOfModules.RingedSite.DeRham.basicForm
    (RingedSpace.DeRham.structureMap q.toLRSHom.toShHom)
    c (op ⊤) 1 fs

/--
`equationForm q fs` is the basic form with coefficient one and ordered differential entries
`fs`.
-/
theorem equationForm_apply (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) :
    equationForm q fs =
      SheafOfModules.RingedSite.DeRham.basicForm
        (RingedSpace.DeRham.structureMap q.toLRSHom.toShHom)
        c (op ⊤) 1 fs := sorry

/--
The morphism from the monoidal unit classified by the ordered equation form.
-/
noncomputable def equationFormMorphism (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) :
    𝟙_ (X.Modules) ⟶ relativeForm q c :=
  RingedSpace.tensorUnitToUnitModule X.toRingedSpace ≫
    RingedSpace.topSectionMorphism
      (RingedSpace.DeRham.form.{u} q.toLRSHom.toShHom c) (equationForm q fs)

/--
The equation-form morphism is the tensor-unit comparison followed by the morphism
classified by `equationForm q fs`.
-/
theorem equationFormMorphism_eq (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) :
    equationFormMorphism q fs =
      RingedSpace.tensorUnitToUnitModule X.toRingedSpace ≫
        RingedSpace.topSectionMorphism
          (RingedSpace.DeRham.form.{u} q.toLRSHom.toShHom c) (equationForm q fs) := sorry

/--
Right exterior multiplication by the ordered equation form.
-/
noncomputable def wedgeWithEquations (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    relativeForm q p ⟶ relativeForm q (p + c) :=
  (Scheme.Modules.fromRingedSpace X).map
    ((ρ_ (RingedSpace.DeRham.form.{u} q.toLRSHom.toShHom p)).inv ≫
      (RingedSpace.DeRham.form.{u} q.toLRSHom.toShHom p ◁
        equationFormMorphism q fs) ≫
      SheafOfModules.RingedSite.DeRham.formWedge
        (RingedSpace.DeRham.structureMap q.toLRSHom.toShHom) p c)

/--
On local sections, `wedgeWithEquations` is right wedge multiplication by
`d(fs 0) ∧ ⋯ ∧ d(fs (c - 1))`.
-/
theorem wedgeWithEquations_apply (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    wedgeWithEquations q fs p =
      (Scheme.Modules.fromRingedSpace X).map
        ((ρ_ (RingedSpace.DeRham.form.{u} q.toLRSHom.toShHom p)).inv ≫
          (RingedSpace.DeRham.form.{u} q.toLRSHom.toShHom p ◁
            equationFormMorphism q fs) ≫
          SheafOfModules.RingedSite.DeRham.formWedge
            (RingedSpace.DeRham.structureMap q.toLRSHom.toShHom) p c) := sorry

/--
Right wedge multiplication by the differential of one selected equation.
-/
noncomputable def wedgeWithEquation (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (i : Fin c) (p : ℕ) :
    relativeForm q p ⟶ relativeForm q (p + 1) :=
  wedgeWithEquations q (fun _ : Fin 1 ↦ fs i) p

/--
The direct-sum map whose `i`-th component wedges with `d(fs i)` after restriction to the
common closed zero locus.
-/
noncomputable def relationMap (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    (⨁ (fun _ : Fin c ↦
      (ModuleCech.LocalCohomology.zeroLocusPullback fs).obj
        (relativeForm q p))) ⟶
      (ModuleCech.LocalCohomology.zeroLocusPullback fs).obj
        (relativeForm q (p + 1)) :=
  biproduct.desc fun i ↦
    (ModuleCech.LocalCohomology.zeroLocusPullback fs).map
      (wedgeWithEquation q fs i p)

/--
The explicit quotient presentation of `Ω^p` on the closed subscheme cut out by `fs`: first
quotient by the equations, then by the relations `d(fs i) ∧ Ω^(p-1)`.
-/
noncomputable def presentation (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) : (p : ℕ) →
    SheafOfModules.ClosedSubset.Modules X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus fs)
  | 0 => (ModuleCech.LocalCohomology.zeroLocusPullback fs).obj
      (relativeForm q 0)
  | p + 1 => cokernel (relationMap q fs p)

/--
The canonical projection from restricted ambient forms to their closed-subscheme quotient
presentation.
-/
noncomputable def projection (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) : (p : ℕ) →
    (ModuleCech.LocalCohomology.zeroLocusPullback fs).obj
        (relativeForm q p) ⟶ presentation q fs p
  | 0 => 𝟙 _
  | p + 1 => cokernel.π (relationMap q fs p)

/--
The closed-support quotient realization of `Ω^p_{Z/S}` for the canonical subscheme `Z`
cut out by `fs`.
-/
noncomputable def source (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    SheafOfModules.ClosedSubset.Modules X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus fs) :=
  presentation q fs p

/--
Before descent, the equation Gysin morphism takes the local-cohomology class and then applies
right wedge multiplication by the ordered equation form.
-/
noncomputable def preMap (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    (ModuleCech.LocalCohomology.zeroLocusPullback fs).obj
        (relativeForm q p) ⟶
      (ModuleCech.LocalCohomology.cohomologyFunctor fs).obj
        (relativeForm q (p + c)) :=
  (ModuleCech.LocalCohomology.quotientClassMap fs).app
      (relativeForm q p) ≫
    (ModuleCech.LocalCohomology.cohomologyFunctor fs).map
      (wedgeWithEquations q fs p)

/--
The pre-Gysin morphism kills every relation generated by wedging with one `d(fs i)`.
-/
theorem relationMap_preMap (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    relationMap q fs p ≫ preMap q fs (p + 1) = 0 := sorry

/--
The degree-`p` Gysin morphism associated to the ordered equations `fs`, from the quotient
realization of `Ω^p_{Z/S}` to `H^c_Z(Ω^(p+c)_{X/S})`.
-/
noncomputable def map (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) : (p : ℕ) →
    source q fs p ⟶
      (ModuleCech.LocalCohomology.cohomologyFunctor fs).obj
        (relativeForm q (p + c))
  | 0 => preMap q fs 0
  | p + 1 => cokernel.desc (relationMap q fs p) (preMap q fs (p + 1))
      (relationMap_preMap q fs p)

/--
Composing the canonical projection with the Gysin morphism gives the local-cohomology class
of a lift, followed by right wedge multiplication with all the ordered equation differentials.
-/
theorem projection_map (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    projection q fs p ≫ map q fs p = preMap q fs p := sorry

end AlgebraicGeometry.Scheme.DeRham.Gysin

end
