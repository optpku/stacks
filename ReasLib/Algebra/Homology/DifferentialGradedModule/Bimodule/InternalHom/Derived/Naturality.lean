/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.QuasiIso
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Linear.Right

/-!
# Naturality of Derived Fixed-Source Internal Hom

The contravariant precomposition map on DG homotopy categories induces the canonical natural
transformation on total right-derived internal-Hom functors. No derived morphism is chosen from
an existence proof: the only input map is the explicit homotopy-level precomposition map.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory

namespace DifferentialGradedBimodule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}
variable {T T' T'' : DifferentialGradedBimodule.{u, v, w, x} A B}

/-- The map between the homotopy-level sources of derived internal Hom induced by
contravariant precomposition. -/
@[stacks 0BYV "derived internal-Hom source map in the bimodule variable"]
def derivedSourceMap (f : T ⟶ T') :
    derivedSourceFunctor T' ⟶ derivedSourceFunctor T :=
  Functor.whiskerRight (precompK f) (DifferentialGradedModule.Derived.Q A)

/-- A component of `derivedSourceMap` is localization of the explicit homotopy-level
precomposition map. -/
@[simp, stacks 0BYV "component of the derived internal-Hom source map"]
theorem derivedSourceMap_app (f : T ⟶ T')
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    (derivedSourceMap f).app P =
      (DifferentialGradedModule.Derived.Q A).map ((precompK f).app P) := sorry

/-- The identity bimodule morphism induces the identity map of derived sources. -/
@[simp, stacks 0BYV "identity law for derived internal-Hom source maps"]
theorem derivedSourceMap_id (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    derivedSourceMap (𝟙 T) = 𝟙 (derivedSourceFunctor T) := sorry

/-- Contravariance reverses composition on the homotopy-level derived sources. -/
@[simp, stacks 0BYV "composition law for derived internal-Hom source maps"]
theorem derivedSourceMap_comp (f : T ⟶ T') (g : T' ⟶ T'') :
    derivedSourceMap (f ≫ g) = derivedSourceMap g ≫ derivedSourceMap f := sorry

/-- The zero bimodule morphism induces the zero map between derived internal-Hom sources. -/
@[simp]
theorem derivedSourceMap_zero
    (T T' : DifferentialGradedBimodule.{u, v, w, x} A B) :
    derivedSourceMap (0 : T ⟶ T') = 0 := sorry

/-- Maps between derived internal-Hom sources are additive in the bimodule morphism. -/
@[simp]
theorem derivedSourceMap_add (f g : T ⟶ T') :
    derivedSourceMap (f + g) = derivedSourceMap f + derivedSourceMap g := sorry

/-- Maps between derived internal-Hom sources are `R`-linear in the bimodule morphism. -/
@[simp]
theorem derivedSourceMap_smul (r : R) (f : T ⟶ T') :
    derivedSourceMap (r • f) = r • derivedSourceMap f := sorry

/-- A bimodule isomorphism induces the explicit contravariant isomorphism between the sources
of the two derived internal-Hom functors. -/
@[stacks 0BYV "derived internal-Hom source isomorphism"]
def derivedSourceIso (e : T ≅ T') : derivedSourceFunctor T' ≅ derivedSourceFunctor T :=
  Functor.isoWhiskerRight (precompKIso e) (DifferentialGradedModule.Derived.Q A)

/-- The forward map of the source isomorphism is localization of precomposition by `e.hom`. -/
@[simp, stacks 0BYV "forward derived internal-Hom source isomorphism"]
theorem derivedSourceIso_hom (e : T ≅ T') :
    (derivedSourceIso e).hom = derivedSourceMap e.hom := sorry

/-- The inverse of the source isomorphism is induced by the inverse bimodule morphism. -/
@[simp, stacks 0BYV "inverse derived internal-Hom source isomorphism"]
theorem derivedSourceIso_inv (e : T ≅ T') :
    (derivedSourceIso e).inv = derivedSourceMap e.inv := sorry

/-- Lemma 22.31.3 (1) (0BYV): a bimodule morphism acts contravariantly on total
right-derived internal-Hom functors. -/
@[stacks 0BYV "contravariant naturality of derived internal Hom"]
noncomputable def derivedNatTrans (f : T ⟶ T') :
    derivedFunctor T' ⟶ derivedFunctor T :=
  Functor.RightDerived.mapNatTrans (DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B) (derivedSourceMap f)

/-- The derived precomposition transformation is characterized by the universal comparison
square. -/
@[reassoc (attr := simp), stacks 0BYV "derived internal-Hom naturality comparison square"]
theorem derivedNatTrans_fac (f : T ⟶ T') :
    derivedUnit T' ≫
        Functor.whiskerLeft (DifferentialGradedModule.Derived.Q B) (derivedNatTrans f) =
      derivedSourceMap f ≫ derivedUnit T := sorry

/-- Derived precomposition by the identity bimodule morphism is the identity. -/
@[simp, stacks 0BYV "identity law for derived internal-Hom transformations"]
theorem derivedNatTrans_id (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    : derivedNatTrans (𝟙 T) = 𝟙 (derivedFunctor T) := sorry

/-- Contravariant derived precomposition reverses composition. -/
@[simp, stacks 0BYV "composition law for derived internal-Hom transformations"]
theorem derivedNatTrans_comp (f : T ⟶ T') (g : T' ⟶ T'')
    : derivedNatTrans (f ≫ g) = derivedNatTrans g ≫ derivedNatTrans f := sorry

/-- The zero bimodule morphism induces the zero derived internal-Hom transformation. -/
@[simp]
theorem derivedNatTrans_zero
    (T T' : DifferentialGradedBimodule.{u, v, w, x} A B) :
    derivedNatTrans (0 : T ⟶ T') = 0 := sorry

/-- Derived internal-Hom transformations are additive in the bimodule morphism. -/
@[simp]
theorem derivedNatTrans_add (f g : T ⟶ T') :
    derivedNatTrans (f + g) = derivedNatTrans f + derivedNatTrans g := sorry

/-- Derived internal-Hom transformations are `R`-linear in the bimodule morphism. -/
@[simp]
theorem derivedNatTrans_smul (r : R) (f : T ⟶ T') :
    derivedNatTrans (r • f) = r • derivedNatTrans f := sorry

/-- Total derived internal Hom is a functor contravariant in its bimodule source. -/
@[stacks 0BYV "derived internal Hom as a functor of the bimodule"]
noncomputable def derivedBimoduleFunctor
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} B ⥤
        DifferentialGradedModule.Derived.Category.{u, v} A) where
  obj T := derivedFunctor T.unop
  map f := derivedNatTrans f.unop
  map_id := sorry
  map_comp := sorry

/-- The value of `derivedBimoduleFunctor` at a bimodule is its fixed-source derived
internal-Hom functor. -/
@[simp, stacks 0BYV "object formula for the derived internal-Hom parameter functor"]
theorem derivedBimoduleFunctor_obj
    (T : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ) :
    (derivedBimoduleFunctor A B).obj T = derivedFunctor T.unop := sorry

/-- The action of `derivedBimoduleFunctor` is the canonical derived precomposition
transformation. -/
@[simp, stacks 0BYV "map formula for the derived internal-Hom parameter functor"]
theorem derivedBimoduleFunctor_map
    {T T' : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ} (f : T ⟶ T') :
    (derivedBimoduleFunctor A B).map f = derivedNatTrans f.unop := sorry

/-- The derived internal-Hom parameter functor is additive. -/
@[stacks 0BYV "additive derived internal Hom parameter functor"]
instance derivedBimoduleFunctorAdditive :
    (derivedBimoduleFunctor A B).Additive := sorry

/-- The derived internal-Hom parameter functor is `R`-linear. -/
@[stacks 0BYV "linear derived internal Hom parameter functor"]
instance derivedBimoduleFunctorLinear :
    Functor.Linear R (derivedBimoduleFunctor A B) := sorry

/-- A strict bimodule isomorphism induces a contravariant isomorphism between total
right-derived internal-Hom functors. -/
@[stacks 0BYV "derived internal-Hom natural isomorphism in the bimodule variable"]
noncomputable def derivedNatIso (e : T ≅ T') :
    derivedFunctor T' ≅ derivedFunctor T :=
  Functor.RightDerived.mapNatIso (DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B) (derivedSourceIso e)

/-- The forward map of the derived isomorphism is the canonical derived precomposition
transformation. -/
@[simp, stacks 0BYV "forward derived internal-Hom natural isomorphism"]
theorem derivedNatIso_hom (e : T ≅ T') :
    (derivedNatIso e).hom = derivedNatTrans e.hom := sorry

/-- The inverse of the derived internal-Hom isomorphism is induced by the inverse bimodule map. -/
@[simp, stacks 0BYV "inverse derived internal-Hom natural isomorphism"]
theorem derivedNatIso_inv (e : T ≅ T') :
    (derivedNatIso e).inv = derivedNatTrans e.inv := sorry

/-- Lemma 22.31.3 (2) (0BYV): precomposition by a bimodule quasi-isomorphism is an isomorphism
between total right-derived internal-Hom functors. -/
@[stacks 0BYV "derived internal Hom inverts bimodule quasi-isomorphisms"]
theorem derivedNatTrans_isIso_of_quasiIso (f : T ⟶ T')
    (hf : DifferentialGradedBimodule.quasiIso A B f) :
    IsIso (derivedNatTrans f) := sorry

/-- The contravariant derived internal-Hom parameter functor inverts all bimodule
quasi-isomorphisms. -/
@[stacks 0BYV "derived internal Hom descends along bimodule quasi-isomorphisms"]
theorem derivedBimoduleFunctor_inverts
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    (DifferentialGradedBimodule.quasiIso A B).op.IsInvertedBy
      (derivedBimoduleFunctor A B) := sorry

#synth (derivedBimoduleFunctor A B).Additive
#synth Functor.Linear R (derivedBimoduleFunctor A B)

end DifferentialGradedBimodule.InternalHom
