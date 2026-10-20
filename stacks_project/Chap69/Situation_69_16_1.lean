module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

/- Situation 69.16.1 (1): Here S is a scheme and X is a quasi-compact and quasi-separated
algebraic space over S with the following property: for every quasi-coherent 𝒪_X-module F
we have H^1(X, F) = 0. -/
@[stacks 07UY] #check
  (AlgebraicGeometry.AlgebraicSpace.HasVanishingH1 :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})], Prop)
#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Situation 69.16.1 (2): We set A = Γ(X, 𝒪_X). -/
@[stacks 07UY] #check
  (AlgebraicGeometry.AlgebraicSpace.globalSectionsRing :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.AlgebraicSpace S → CommRingCat.{u})
