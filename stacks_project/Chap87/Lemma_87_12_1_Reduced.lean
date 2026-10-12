/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import stacks_project.Chap87.Definition_87_11_1_Representable

/-!
# Reduced algebraic spaces on a chosen big fppf site

A sheaf on `(Sch/S)_fppf` is a reduced algebraic space when it is an algebraic
space and admits a relatively étale locally surjective atlas from a sheafified
representable of a reduced object of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf on `(Sch/S)_fppf` is a reduced algebraic space when it is an
algebraic space and admits a relatively étale locally surjective atlas from a
reduced object of the site. -/
class IsReduced {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAlgebraicSpace X where
  /-- There is a relatively étale locally surjective atlas from a sheafified
  representable of a reduced object of `(Sch/S)_fppf`. -/
  exists_reduced_atlas :
    ∃ (U : 𝒮.bigSite S)
      (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
        relativelyEtale p ∧ Sheaf.IsLocallySurjective p ∧
          AlgebraicGeometry.IsReduced ((𝒮.bigToScheme S).obj U)

/-- The sheafified representable of a reduced object of `(Sch/S)_fppf` is a
reduced algebraic space. -/
instance instIsReduced_sheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigSite S)
    [AlgebraicGeometry.IsReduced ((𝒮.bigToScheme S).obj U)] :
    IsReduced ((𝒮.bigTopology S).sheafifiedRepresentable U) := sorry

/-- A sheaf is a reduced algebraic space iff it is an algebraic space and
admits a relatively étale locally surjective atlas from a reduced object of
the site. -/
theorem IsReduced.iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsReduced X ↔
      IsAlgebraicSpace X ∧
        ∃ (U : 𝒮.bigSite S)
          (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
            relativelyEtale p ∧ Sheaf.IsLocallySurjective p ∧
              AlgebraicGeometry.IsReduced ((𝒮.bigToScheme S).obj U) := sorry

/-- A reduced algebraic space unpacks as an algebraic space together with a
relatively étale locally surjective atlas from a reduced object of the site. -/
theorem IsReduced.spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsReduced X] :
    IsAlgebraicSpace X ∧
      ∃ (U : 𝒮.bigSite S)
        (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
          relativelyEtale p ∧ Sheaf.IsLocallySurjective p ∧
            AlgebraicGeometry.IsReduced ((𝒮.bigToScheme S).obj U) := sorry


end AlgebraicGeometry.ChosenBigFppfSite
