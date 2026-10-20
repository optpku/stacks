module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Colimit.Separated
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/-! Lemma 81.3.4 -/
@[stacks 0GFP] #check
  (AlgebraicGeometry.AlgebraicSpace.isColimit_of_separatedOver :
    ∀ {J : Type v} [Category.{v} J] [Small.{u} J]
      {S : Scheme.{u}} {B : AlgebraicSpace S} (D : J ⥤ Over B) (c : Cocone D)
      (h_sep : ∀ i, Separated (D.obj i).hom) (h_pt : Separated c.pt.hom)
      (h_colim : AlgebraicGeometry.AlgebraicSpace.IsColimitAmongSeparated c)
      (h_surj : AlgebraicGeometry.AlgebraicSpace.Surjective
        (AlgebraicGeometry.AlgebraicSpace.coproductToColimit c))
      (h_etale_colim :
        ∀ {U : AlgebraicSpace S} (f : U ⟶ c.pt.left) [Etale f] [Separated f],
          AlgebraicGeometry.AlgebraicSpace.IsColimitAmongSeparated
            (AlgebraicGeometry.AlgebraicSpace.baseChangeCocone c f))
      (h_ess : ∀ sys : AlgebraicGeometry.AlgebraicSpace.CartesianSpacesEtaleSystem D,
        (∀ i, Separated (sys.π.app i)) →
          AlgebraicGeometry.AlgebraicSpace.IsInSeparatedSpacesEtaleEssImage c sys),
      Nonempty (IsColimit c))
