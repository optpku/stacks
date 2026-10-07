module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.FieldChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/- Lemma 53.4.4 (1): if the structure morphism of a proper scheme of dimension at
most one factors through the spectrum of another field, its proper dualizing complex
and curve dualizing module agree with those attached to the factored morphism. -/
@[stacks 0E32]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingObjects_ofFieldFactorization :
    ∀ {k k' : Type u} [Field k] [Field k']
      (X : SchemeOverField k) [IsProper X.hom]
      (f' : X.left ⟶ Spec (CommRingCat.of k'))
      (g : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
      (h_factor : f' ≫ g = X.hom)
      (h_dimension : topologicalKrullDim X.left ≤ 1),
      IsIsomorphic (properDualizingComplex X.hom)
          (@properDualizingComplex k' _ X.left f'
            (isProper_ofFieldFactorization X.hom f' g h_factor)) ∧
        IsIsomorphic (curveDualizingModule X.hom)
          (@curveDualizingModule k' _ X.left f'
            (isProper_ofFieldFactorization X.hom f' g h_factor)))

/- Lemma 53.4.4 (2): after extending the ground field of a proper scheme of
dimension at most one, derived pullback of its proper dualizing complex and ordinary
pullback of its curve dualizing module agree with the corresponding objects on the
base-changed scheme. -/
@[stacks 0E32]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingObjects_baseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left ≤ 1),
      let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
      IsIsomorphic
          ((DerivedQCoh.pullback (pullback.fst X.hom g)).obj
            (properDualizingComplex X.hom))
          (properDualizingComplex (pullback.snd X.hom g)) ∧
        IsIsomorphic
          ((Scheme.Modules.pullback (pullback.fst X.hom g)).obj
            (curveDualizingModule X.hom))
          (curveDualizingModule (pullback.snd X.hom g)))

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
