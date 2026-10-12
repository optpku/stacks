/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Symmetric

/-!
# Closed cochain complexes of modules

Integer cochain complexes of modules carry the canonical closed structure built from products of
degreewise module internal Homs. The resulting ambient internal Hom is canonically isomorphic to
the module-valued enriched Hom complex. This file owns the instance and that comparison; generic
closed-monoidal operations live in `ReasLib.CategoryTheory.Monoidal.Closed`.

@stack 0GWQ
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex ComplexShape

namespace CategoryTheory.CochainComplex.InternalHom

variable {R : Type u} [CommRing R]

/-- The canonical closed structure on integer cochain complexes of modules. -/
@[stacks 0GWQ "closed category of module cochain complexes", instance_reducible]
noncomputable instance moduleCat : MonoidalClosed (CochainComplex (ModuleCat R) ℤ) :=
  monoidalClosed

/-- The degreewise product comparison commutes with the two Hom-complex differentials. -/
theorem degreeIso_hom_comm
    (K L : CochainComplex (ModuleCat R) ℤ) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (degreeIso R K L i).hom ≫ (moduleComplex R K L).d i j =
      ((ihom K).obj L).d i j ≫ (degreeIso R K L j).hom := sorry

/-- The ambient closed internal Hom agrees canonically with the module-valued enriched Hom
complex. -/
@[stacks 0GWQ "closed and enriched Hom-complex comparison"]
noncomputable def moduleComplexIso
    (K L : CochainComplex (ModuleCat R) ℤ) :
    (ihom K).obj L ≅ moduleComplex R K L :=
  HomologicalComplex.Hom.isoOfComponents
    (degreeIso R K L) (degreeIso_hom_comm K L)

/-- The degree-`n` component of `moduleComplexIso` is the canonical product decomposition. -/
@[simp]
theorem moduleComplexIso_hom_f
    (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (moduleComplexIso K L).hom.f n = (degreeIso R K L n).hom := sorry

/-- The inverse degree-`n` component of `moduleComplexIso` is the inverse product
decomposition. -/
@[simp]
theorem moduleComplexIso_inv_f
    (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (moduleComplexIso K L).inv.f n = (degreeIso R K L n).inv := sorry

/-- The comparison intertwines ambient precomposition with source functoriality of the enriched
Hom complex. -/
theorem moduleComplexIso_natural_source
    {K K' L : CochainComplex (ModuleCat R) ℤ} (f : K' ⟶ K) :
    (MonoidalClosed.pre f).app L ≫ (moduleComplexIso K' L).hom =
      (moduleComplexIso K L).hom ≫
        CochainComplex.HomComplex.map R f (𝟙 L) := sorry

/-- The comparison intertwines ambient postcomposition with target functoriality of the enriched
Hom complex. -/
theorem moduleComplexIso_natural_target
    (K : CochainComplex (ModuleCat R) ℤ)
    {L L' : CochainComplex (ModuleCat R) ℤ} (g : L ⟶ L') :
    (ihom K).map g ≫ (moduleComplexIso K L').hom =
      (moduleComplexIso K L).hom ≫
        CochainComplex.HomComplex.map R (𝟙 K) g := sorry

/-- After the closed/enriched comparison, the canonical enriched projection is the ambient
product projection. -/
theorem moduleComplexIso_hom_f_proj
    (K L : CochainComplex (ModuleCat R) ℤ) (n p : ℤ) :
    (moduleComplexIso K L).hom.f n ≫ proj R K L n p =
      Pi.π (family K L n) p := sorry

/-- At a fixed source, the ambient and module-valued internal-Hom functors are naturally
isomorphic. -/
@[stacks 0GWQ "fixed-source closed/enriched Hom comparison"]
noncomputable def moduleComplexNatIsoApp
    (K : (CochainComplex (ModuleCat R) ℤ)ᵒᵖ) :
    (MonoidalClosed.internalHom.obj K) ≅
      (CochainComplex.HomComplex.curried (C := ModuleCat R) R).obj K :=
  NatIso.ofComponents
    (fun L ↦ moduleComplexIso K.unop L)
    (moduleComplexIso_natural_target K.unop)

/-- The fixed-source comparison is natural in the contravariant source variable. -/
theorem moduleComplexNatIsoApp_naturality
    {K K' : (CochainComplex (ModuleCat R) ℤ)ᵒᵖ} (f : K ⟶ K') :
    MonoidalClosed.internalHom.map f ≫ (moduleComplexNatIsoApp (R := R) K').hom =
      (moduleComplexNatIsoApp (R := R) K).hom ≫
        (CochainComplex.HomComplex.curried (C := ModuleCat R) R).map f := sorry

/-- The closed internal Hom and the module-valued enriched Hom agree as bifunctors. -/
@[stacks 0GWQ "closed and enriched Hom-complex bifunctor comparison"]
noncomputable def moduleComplexNatIso :
    MonoidalClosed.internalHom ≅
      CochainComplex.HomComplex.curried (C := ModuleCat R) R :=
  NatIso.ofComponents
    (moduleComplexNatIsoApp (R := R))
    (moduleComplexNatIsoApp_naturality (R := R))

/-- The component of `moduleComplexNatIso` is the canonical Hom-complex comparison. -/
@[simp]
theorem moduleComplexNatIso_app_app
    (K : (CochainComplex (ModuleCat R) ℤ)ᵒᵖ)
    (L : CochainComplex (ModuleCat R) ℤ) :
    ((moduleComplexNatIso (R := R)).app K).app L =
      moduleComplexIso K.unop L := sorry

end CategoryTheory.CochainComplex.InternalHom
