/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.Presheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The identity morphism of a scheme, regarded as a finite étale object over that scheme. -/
noncomputable def finiteEtaleTerminal (X : Scheme.{u}) : FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (finiteEtaleMorphism.id_mem X)

/-- The identity finite étale object is terminal among finite étale objects over its base. -/
noncomputable def finiteEtaleTerminal_isTerminal (X : Scheme.{u}) :
    IsTerminal (finiteEtaleTerminal X) :=
  MorphismProperty.Over.mkIdTerminal finiteEtaleMorphism X

/-- For finite étale objects `U` and `V` over `X`, their relative morphisms are represented
by a finite étale object over `X`. -/
theorem exists_finiteEtaleHom {X : Scheme.{u}} (U V : FiniteEtale X) :
    ∃ W : FiniteEtale X,
      Nonempty
        ((RelativeHom.functor (Over.mk U.hom) (Over.mk V.hom)).RepresentableBy
          (Over.mk W.hom)) := sorry

end AlgebraicGeometry.Scheme
