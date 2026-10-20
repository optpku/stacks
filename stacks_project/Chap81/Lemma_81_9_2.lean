/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare.Construction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 81.9.2. An open immersion and a separated étale morphism of algebraic
spaces over a scheme yields the canonical quotient pushout. -/
@[stacks 0DVJ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.isPushout_ofOpenSeparatedEtale :
    ∀ {S : Scheme.{u}} {U V V' : AlgebraicSpace S}
      (ι : V' ⟶ V) (f' : V' ⟶ U) [AlgebraicSpace.IsOpenImmersion ι] [AlgebraicSpace.Etale f'] [AlgebraicSpace.Separated f'],
      IsPushout ι f'
        (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.inl ι f')
        (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.inr ι f'))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.instIsElementaryDistinguishedSquare_ofOpenSeparatedEtale :
    ∀ {S : Scheme.{u}} {U V V' : AlgebraicSpace S}
      (ι : V' ⟶ V) (f' : V' ⟶ U) [AlgebraicSpace.IsOpenImmersion ι] [AlgebraicSpace.Etale f'] [AlgebraicSpace.Separated f'],
      AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
        (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.inr ι f')
        (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.inl ι f'))
