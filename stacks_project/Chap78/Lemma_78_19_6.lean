module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Restriction
import StacksCheckRecall

/-!
# Restriction of pre-equivalence relations and quotient sheaves

Restriction induces an injective map of fppf quotient sheaves, and a sheaf-surjective
morphism, in particular a singleton fppf covering, induces an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 78.19.6. Restricting a pre-equivalence relation induces an injective map
of quotient sheaves. It is an isomorphism if the morphism is surjective as a map
of sheaves, in particular if it is a singleton fppf covering. -/
@[stacks 046P]
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafMap_isLocallyInjective :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (hP : P.IsPreEquivalence),
    Sheaf.IsLocallyInjective (P.quotientSheafMap g))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafMap_isIso_of_locallySurjective :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (hP : P.IsPreEquivalence)
    (hg : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) g.left),
    IsIso (P.quotientSheafMap g))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafMap_isIso_of_fppfCovering :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (hP : P.IsPreEquivalence)
    [FppfCovering (fun _ : PUnit ↦ U'.left) (fun _ ↦ g.left)],
    IsIso (P.quotientSheafMap g))
