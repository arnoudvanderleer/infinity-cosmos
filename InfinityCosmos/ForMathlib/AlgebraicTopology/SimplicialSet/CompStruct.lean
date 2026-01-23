import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet}
variable {x₀ x₁ x₂ x₀' x₁' x₂' : X _⦋0⦌}

namespace Edge

variable (e : Edge x₀ x₁)
variable (hx₀ : x₀ = x₀')
variable (hx₁ : x₁ = x₁')

lemma map_edge
  (f : X ⟶ Y)
  : (e.map f).edge = f.app _ e.edge
  := rfl

def ofEq
  : Edge x₀' x₁'
  where
    edge := e.edge
    src_eq := e.src_eq.trans hx₀
    tgt_eq := e.tgt_eq.trans hx₁

namespace CompStruct

variable {e₀₁ : Edge x₀ x₁} {e₀₁' : Edge x₀' x₁'}
variable {e₁₂ : Edge x₁ x₂} {e₁₂' : Edge x₁' x₂'}
variable {e₀₂ : Edge x₀ x₂} {e₀₂' : Edge x₀' x₂'}
variable (c : CompStruct e₀₁ e₁₂ e₀₂)

lemma d₂ : X.δ 2 c.simplex = e₀₁.edge := c.toTruncated.d₂
lemma d₀ : X.δ 0 c.simplex = e₁₂.edge := c.toTruncated.d₀
lemma d₁ : X.δ 1 c.simplex = e₀₂.edge := c.toTruncated.d₁

def ofEq
  (he₀₁' : e₀₁.edge = e₀₁'.edge)
  (he₁₂' : e₁₂.edge = e₁₂'.edge)
  (he₀₂' : e₀₂.edge = e₀₂'.edge)
  : CompStruct e₀₁' e₁₂' e₀₂'
  where
    simplex := c.simplex
    d₂ := c.d₂.trans he₀₁'
    d₀ := c.d₀.trans he₁₂'
    d₁ := c.d₁.trans he₀₂'

end CompStruct

structure IsIso (hom : Edge x₀ x₁) where
  inv            : Edge x₁ x₀
  homInvId     : Edge.CompStruct hom inv (Edge.id x₀)
  invHomId     : Edge.CompStruct inv hom (Edge.id x₁)

namespace IsIso

lemma id_comp_id_aux
  {l m n : ℕ}
  {f : ⦋n⦌ ⟶ ⦋m⦌}
  {g : ⦋m⦌ ⟶ ⦋l⦌}
  {h : ⦋n⦌ ⟶ ⦋l⦌}
  (x : X _⦋l⦌)
  (e : f ≫ g = h)
  : X.map f.op (X.map g.op x) = X.map h.op x
  := by
    show ((X.map _ ≫ X.map _) x = X.map _ x)
    rw [← X.map_comp]
    rw [← op_comp]
    congrm X.map (Quiver.Hom.op ?_) x
    exact e

def idCompId (x : X _⦋0⦌) : Edge.CompStruct (Edge.id x) (Edge.id x) (Edge.id x) := .mk
  (X.map (Opposite.op (SimplexCategory.Hom.mk ⟨fun a ↦ 0, monotone_const⟩)) x)
  (by apply id_comp_id_aux; decide)
  (by apply id_comp_id_aux; decide)
  (by apply id_comp_id_aux; decide)

def isIsoId (x : X _⦋0⦌) : IsIso (Edge.id x) where
  inv := Edge.id x
  homInvId := idCompId x
  invHomId := idCompId x

def isIsoInv {hom : Edge x₀ x₁} (I : IsIso hom) : IsIso I.inv where
  inv := hom
  homInvId := I.invHomId
  invHomId := I.homInvId

def map {hom : Edge x₀ x₁} (I : IsIso hom) (f : X ⟶ Y)
  : IsIso (Edge.map hom f) where
  inv := Edge.map I.inv f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

def ofEq {hom : Edge x₀ x₁} {hom' : Edge x₀' x₁'} (I : IsIso hom) (hhom : hom.edge = hom'.edge)
  : IsIso hom'
  where
    inv := I.inv.ofEq (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq]) (by rw [← hom.src_eq, hhom, hom'.src_eq])
    homInvId := I.homInvId.ofEq hhom rfl (by rw [← hom.src_eq, hhom, hom'.src_eq])
    invHomId := I.invHomId.ofEq rfl hhom (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])

end IsIso

end Edge

end SSet
