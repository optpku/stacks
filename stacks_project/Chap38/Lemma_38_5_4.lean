module

import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAtAmbientPoint.BaseChange
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 38.5.4: affine pointed base change with an isomorphism on residue fields
transports a complete dévissage and its uniquely lifted distinguished points. -/
@[stacks 05HK] #check
  (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.baseChange :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
      [AlgebraicGeometry.LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      {x : X} (D : AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint f F x)
      (g : S' ⟶ S) (s' : S') (h_point : g s' = f x) [AlgebraicGeometry.IsAffine S']
      [IsIso (g.residueFieldMap s')] (x' : (pullback f g : AlgebraicGeometry.Scheme))
      (h_x_fst : pullback.fst f g x' = x) (h_x_snd : pullback.snd f g x' = s')
      (z' : ∀ k, (pullback (D.toCompleteDevissageOver.stage k).Z.hom g :
        AlgebraicGeometry.Scheme))
      (h_z_fst : ∀ k, pullback.fst (D.toCompleteDevissageOver.stage k).Z.hom g
        (z' k) = D.z k)
      (h_z_snd : ∀ k, pullback.snd (D.toCompleteDevissageOver.stage k).Z.hom g
        (z' k) = s')
      (y' : ∀ k, (pullback (D.toCompleteDevissageOver.stage k).Y.hom g :
        AlgebraicGeometry.Scheme))
      (h_y_fst : ∀ k, pullback.fst (D.toCompleteDevissageOver.stage k).Y.hom g
        (y' k) = D.y k)
      (h_y_snd : ∀ k, pullback.snd (D.toCompleteDevissageOver.stage k).Y.hom g
        (y' k) = s'),
      AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint
        (pullback.snd f g) (AlgebraicGeometry.Scheme.Modules.baseChangeModule f g F) x')
