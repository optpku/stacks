module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Cube
import StacksCheckRecall

open CategoryTheory

universe uC2 vC2 uC2p vC2p uB2 vB2 uB2p vB2p
  uC1 vC1 uC1p vC1p uB1 vB1 uB1p vB1p w

/- 91.13.1.1: the commutative diagram of morphisms of ringed topoi with vertices
`(Sh(C2), O2)`, `(Sh(C'2), O'2)`, `(Sh(B2), O_{B2})`, `(Sh(B'2), O'2)`,
`(Sh(C1), O1)`, `(Sh(C'1), O'1)`, `(Sh(B1), O_{B1})`, `(Sh(B'1), O'1)`.
The present arrows are `i2`, `f2`, `f'2`, `t2`, `i1`, `f1`, `f'1`, `t1`, and
the named diagonal `g : (Sh(C2), O2) ⟶ (Sh(C1), O1)`; the unlabeled maps
`(Sh(B2), O_{B2}) ⟶ (Sh(B1), O_{B1})` and `(Sh(B'2), O_{B'2}) ⟶ (Sh(B'1), O_{B'1})`
complete the base face. The morphism `(Sh(C'2), O'2) ⟶ (Sh(C'1), O'1)` is not
part of the diagram. In the wrapping lemma the four horizontals `i2`, `t2`,
`i1`, `t1` are first-order thickenings; that hypothesis is not recorded on
`OpenCube`. -/
@[stacks 08UH] #check
  (@RingedSite.ToposHom.OpenCube :
    ∀ {C2 : RingedSite.{uC2, vC2, w}} {C2' : RingedSite.{uC2p, vC2p, w}}
      {B2 : RingedSite.{uB2, vB2, w}} {B2' : RingedSite.{uB2p, vB2p, w}}
      {C1 : RingedSite.{uC1, vC1, w}} {C1' : RingedSite.{uC1p, vC1p, w}}
      {B1 : RingedSite.{uB1, vB1, w}} {B1' : RingedSite.{uB1p, vB1p, w}}
      [C2.siteTopology.HasSheafCompose (forget RingCat.{w})]
      [C2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
      [B2.siteTopology.HasSheafCompose (forget RingCat.{w})]
      [B2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
      [C1.siteTopology.HasSheafCompose (forget RingCat.{w})]
      [C1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
      [B1.siteTopology.HasSheafCompose (forget RingCat.{w})]
      [B1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
      (back : RingedSite.ToposHom.CommSquare C2 C2' B2 B2')
      (front : RingedSite.ToposHom.CommSquare C1 C1' B1 B1'),
      Type
        (max
          (max
            (max
              (max
                (max
                  (max
                    (max
                      (max
                        (max (max (max (max (max uB1 uB1p) uB2) uB2p) uC1) uC2)
                          vB1)
                        vB1p)
                      vB2)
                    vB2p)
                  vC1)
                vC2)
              (w + 1))))
