module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RegularSection
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open scoped AlgebraicGeometry

universe u

/- Lemma 71.7.5
A global function on an algebraic space is regular if and only if it is a
nonzerodivisor in every geometric étale stalk, on every affine étale chart,
or becomes regular on some surjective étale scheme cover.
-/
@[stacks 0844] #check
  (AlgebraicGeometry.AlgebraicSpace.isRegularStructureSection_iff_stalkwise :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (f : globalSectionsRing X),
      IsRegularStructureSection f ↔
        ∀ (xbar : GeometricPoint X) (U : smallEtaleSite X)
          (l : xbar.toSmallEtalePoint.fiber.obj U),
          IsSMulRegular (structureSheafStalk xbar) (structureSectionGerm xbar U l f))

@[stacks 0844] #check
  (AlgebraicGeometry.AlgebraicSpace.isRegularStructureSection_iff_forall_affineEtale :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (f : globalSectionsRing X),
      IsRegularStructureSection f ↔
        ∀ U : affineEtaleSite X,
          IsSMulRegular Γ((smallEtaleToScheme X).obj U.obj, ⊤)
            (restrictGlobalSection U.obj f))

@[stacks 0844] #check
  (AlgebraicGeometry.AlgebraicSpace.isRegularStructureSection_iff_exists_surjectiveEtale :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (f : globalSectionsRing X),
      IsRegularStructureSection f ↔
        ∃ U : smallEtaleSite X,
          Surjective U.hom ∧
            Scheme.IsRegularStructureSection (restrictGlobalSection U f))
