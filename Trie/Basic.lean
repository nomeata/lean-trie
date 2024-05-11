import Lean.Data.AssocList

open Lean (AssocList)

set_option autoImplicit false

universe u
universe v
variable {α : Type u}
variable [DecidableEq α]
variable {β : Type v}


def fun_upd : (α → Option β) → α → (Option β → β) → (α → Option β) :=
  fun f x k x' => if x' = x then some (k ((f x'))) else f x'

theorem fun_upd_eq (f : α → Option β) (x : α) (k : Option β → β) :
  (fun_upd f x k x) = some (k (f x)) := by
  simp [fun_upd]

theorem fun_upd_ne (f : α → Option β) (x₁ x₂ : α) (k : Option β → β) (h : x₂ ≠ x₁):
  (fun_upd f x₁ k x₂) = f x₂ := by
  simp [fun_upd, h]

theorem map_fun_upd_congr {β'}
    (f : α → Option β) (t : β → β') (x : α) (k : Option β → β) (k' : Option β' → β')
    (h : ∀ y?, t (k y?) = k' (y?.map t))
    : (fun x' => Option.map t (fun_upd f x k x')) = fun_upd (fun x' => Option.map t (f x')) x k' := by
  unfold fun_upd
  ext k' : 1
  split
  · simp [fun_upd, Option.map, h]
  · rfl

section Prefix

def commonPrefix : (xs ys : List α) → List α
  | _ , [] => []
  | [], _  => []
  | x::xs, y::ys =>
    if x = y then
      x :: commonPrefix xs ys
    else
      []

def hasPrefix : (xs ys : List α) → Bool
  | _ , [] => true
  | [], _ => false
  | x::xs, y::ys =>
    if x = y then
      hasPrefix xs ys
    else
      false

theorem commonPrefix_of_hasPrefix (xs ys : List α) (h : hasPrefix xs ys = true) :
    commonPrefix xs ys = ys := by
  induction xs, ys using commonPrefix.induct
  case case1 => simp [commonPrefix]
  case case2 => simp [hasPrefix] at h
  case case3 x xs ys => simp_all [commonPrefix, hasPrefix]
  case case4 x xs ys => simp_all [commonPrefix, hasPrefix]

end Prefix

namespace Trie.Abstract

/--
A very abstract idea of a trie data structure. We prove the relevant theorems about
their properties here, and show that more refined implementations behave like these.
-/
inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (c : α → Option (Trie α β)) : Trie α β

namespace Trie

def val : Trie α β → Option β | .node v _ => v
@[simp] theorem val_eq (v : Option β) (cs : α → Option (Trie α β)) : val (.node v cs) = v := by rfl

def c : Trie α β → (α → Option (Trie α β)) | .node _ c => c
@[simp] theorem c_eq (v : Option β) (cs : α → Option (Trie α β)) : c (.node v cs) = cs := by rfl

def empty : Trie α β := .node none (fun _ => .none)

def insert (t : Trie α β) : List α → β → Trie α β
  | [], v => .node (some v) t.c
  | k::ks, v => .node t.val <|
      fun_upd t.c k fun t => t.getD empty |>.insert ks v

def find? (t : Trie α β) : List α → Option β
  | [] => t.val
  | k::ks => match t.c k with
    | none => none
    | some t => t.find? ks

@[simp]
theorem find?_empty (k : List α) : (empty : Trie α β).find? k = none :=  by
  cases k <;> simp [empty, find?]

theorem find?_insert_eq (t : Trie α β) (k : List α) (v : β) :
    (t.insert k v).find? k = some v := by
  induction k generalizing t with
  | nil => simp [insert, find?, val]
  | cons k ks ih =>
    cases t with | _ v' c =>
    simpa [insert, find?, fun_upd] using ih _

theorem find?_insert_neq (t : Trie α β) (k k' : List α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  induction k generalizing t k' with
  | nil =>
    cases k' with | nil => contradiction | cons k' ks' =>
    cases t with | _ v' c =>
    simp [find?, insert]
  | cons k ks ih =>
    cases t with | _ v' c =>
    cases k' with
    | nil => simp [find?, insert]
    | cons k' ks' =>
      if hk : k' = k then
        subst k'
        have : ks ≠ ks' := by intro h; apply hne; cases h; rfl
        simp [insert, find?, hne, fun_upd, Option.getD, ih, this]
        cases c k <;> simp
      else
        simp [insert, find?, fun_upd, hk]


end Trie
end Trie.Abstract

namespace Lean.AssocList

/-! Missing definitions and lemmas about Lean.AssocList -/

def upsert (xs : AssocList α β) (k : α) (f : Option β → β) : AssocList α β :=
  match xs with
  | .cons k' v xs =>
    if k = k' then
      .cons k' (f (some v)) xs
    else
      .cons k' v (upsert xs k f)
  | .nil => .cons k (f none) .nil

theorem find?_upsert (xs : AssocList α β) (k1 k2 : α) (f : Option β → β) :
    (xs.upsert k1 f).find? k2 = fun_upd (xs.find? ·) k1 f k2 := by
  induction xs, k1, f using upsert.induct
  case case1 f k2 v xs =>
    simp [upsert, find?, fun_upd]
    split
    · simp_all
    · apply (if_neg (Ne.symm _)).symm
      simp_all
  case case2 k1 f k v xs hne ih =>
    simp [upsert, find?, hne, fun_upd]
    split
    next heq =>
      simp at heq; subst heq
      simp [if_neg (Ne.symm _), hne]
    next =>
      rw [ih]
      rfl
  case case3 k1 f =>
    simp [upsert, find?, fun_upd]
    split
    · simp_all
    · apply (if_neg (Ne.symm _)).symm
      simp_all


/-- Fused find and map with sizeOf information -/
def findSized? {γ} [SizeOf β] (xs : AssocList α β) (a : α) (f : (x : β) → (sizeOf x < sizeOf xs) → γ) :
    Option γ :=
  match xs with
  | nil         => none
  | cons k v es => match k == a with
    | true  => some (f v (by simp; omega))
    | false => findSized? es a (fun k _ => f k (by simp; omega))

@[simp]
def findSized?_eq_find?_map
  {γ} [SizeOf β] (xs : AssocList α β) (k : α) (f : (x : β) → γ) :
  findSized? xs k (fun y _ => f y) = (xs.find? k).map f := by
  induction xs <;> simp_all [findSized?, find?, Option.map]
  split <;> simp [*]

def mapSized {γ} [SizeOf β] (xs : AssocList α β) (f : (x : β) → (sizeOf x < sizeOf xs) → γ) :
    AssocList α γ :=
  match xs with
  | nil         => nil
  | cons k v es =>
    cons k (f v (by simp; omega)) (es.mapSized (fun k _ => f k (by simp; omega)))

@[simp]
def mapSized_eq_mapVal {γ} [SizeOf β] (xs : AssocList α β) (f : (x : β) → γ) :
    xs.mapSized (fun y _ => f y) = xs.mapVal f := by
  induction xs <;> simp_all [mapSized, mapVal]

theorem mapVal_upsert_congr {β'}
    (xs : AssocList α β)
    (t : β → β') (k : α) (f : Option β → β) (f' : Option β' → β')
    (h : ∀ y?, t (f y?) = f' (y?.map t))
    : (xs.upsert k f).mapVal t = (xs.mapVal t).upsert k f' := by
  induction xs
  · simp_all [upsert, mapVal]
  · simp only [upsert]
    split
    · simp_all [upsert, mapVal]
    · simp_all [upsert, mapVal]

@[simp] theorem find?_mapVal {β'} (xs : AssocList α β) (f : β → β') (k : α):
  (xs.mapVal f).find? k = (xs.find? k).map f := by
  induction xs
  · simp_all [find?, mapVal]
  · simp only [find?]
    split <;> simp_all


end Lean.AssocList

namespace Trie.AssocList

/-!
Refinement: Using associative lists instead of the abstract function
-/

inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (c : AssocList α (Trie α β)) : Trie α β

namespace Trie

def val : Trie α β → Option β | .node v _ => v
@[simp] theorem val_eq (v : Option β) (cs : AssocList α (Trie α β)) : val (.node v cs) = v := by rfl

def c : Trie α β → AssocList α (Trie α β) | .node _ c => c
@[simp] theorem c_eq (v : Option β) (cs : AssocList α (Trie α β)) : c (.node v cs) = cs := by rfl

def empty : Trie α β := .node none .empty

def insert (t : Trie α β) : List α → β → Trie α β
  | [], v => .node (some v) t.c
  | k::ks, v => .node t.val <|
      t.c.upsert k fun t => (t.getD empty).insert ks v

def find? (t : Trie α β) : List α → Option β
  | [] => t.val
  | k::ks => match t.c.find? k with
    | none => none
    | some t => t.find? ks

/-! We can relate these tries with the more abstract one -/

def abstract : Trie α β → Trie.Abstract.Trie α β
  | .node val? c => .node val? (fun k => c.findSized? k (fun t _ => t.abstract))
decreasing_by simp_wf; omega

@[simp]
theorem val_abstract (t : Trie α β) :
    t.abstract.val = t.val := by
  cases t; simp [Option.map, abstract]

theorem c_abstract (t : Trie α β) :
    t.abstract.c = (fun k => (t.c.find? k).map (·.abstract)) := by
  cases t
  simp [Option.map, abstract]

/-! Use this abstraction function to give specification for the operations -/

@[simp]
theorem empty_spec :
    (empty : Trie α β).abstract = .empty := by
  simp [abstract, empty, Trie.Abstract.Trie.empty]
  rfl

theorem find?_spec (t : Trie α β) (ks : List α):
    t.find? ks = t.abstract.find? ks := by
  induction t, ks using find?.induct
  case case1 t =>
    simp [find?, abstract, Trie.Abstract.Trie.find?]
  case case2 t k ks h =>
    simp [find?, Trie.Abstract.Trie.find?, h, c_abstract]
  case case3 t k ks h ih =>
    simpa only [find?, Trie.Abstract.Trie.find?, h, c_abstract] using ih

theorem insert_spec (t : Trie α β) (ks : List α) (v : β) :
    (insert t ks v).abstract = t.abstract.insert ks v := by
  induction t, ks, v using insert.induct
  case case1 t v =>
    simp [insert, abstract, Trie.Abstract.Trie.insert, c_abstract]
  case case2 t k ks ih =>
    simp [insert, abstract, Trie.Abstract.Trie.insert, c_abstract, AssocList.find?_upsert]
    apply map_fun_upd_congr
    intro t?
    rw [ih]; clear ih
    cases t? <;> simp

/-! And get the theory for free -/

theorem find?_empty (k : List α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, Trie.Abstract.Trie.find?_empty, empty_spec]

theorem find?_insert_eq (t : Trie α β) (k : List α) (v : β) :
    (t.insert k v).find? k = some v := by
  simpa [insert_spec, find?_spec] using Trie.Abstract.Trie.find?_insert_eq _ _ _

theorem find?_insert_neq (t : Trie α β) (k k' : List α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  simpa [insert_spec, find?_spec] using Trie.Abstract.Trie.find?_insert_neq _ _ _ hne _


/- A path is a trie where every node has one child -/

def path (val : Option β) (ps : List α) (t : Trie α β) : Trie α β :=
  match ps with
  | [] => t
  | p::ps => .node val (.cons p (path none ps t) .nil)

@[simp]
theorem path_val (ps : List α) (val : Option β) (h : ps ≠ []) (t : Trie α β):
  (path val ps t).val = val := by
  unfold path
  split; contradiction; simp

@[simp]
theorem path_c (p : α) (ps : List α) (val : Option β) (t : Trie α β):
  (path val (p::ps) t).c = .cons p (path none ps t) .nil := by
  simp [path]

@[simp]
theorem path_eq_insert (ks : List α) (v : β) :
   path none ks (node (some v) .nil) = empty.insert ks v := by
 induction ks <;>
    simp_all [path, AssocList.upsert, insert, empty]

theorem path_insert_eq_commonPrefix (ps ks : List α) (t : Trie α β) (v : β):
    (path none ps t).insert ks v =
      path none (commonPrefix ks ps)
        ((path none (List.drop (commonPrefix ks ps).length ps) t).insert
          (List.drop (commonPrefix ks ps).length ks) v) := by
  induction ks, ps using commonPrefix.induct
  · simp [path, commonPrefix, *]
  · simp [path, commonPrefix, *]
  · simp [path, commonPrefix, AssocList.Trie.insert, AssocList.upsert, *]
  · simp [path, commonPrefix, *]

theorem path_find_of_hasPrefix ps (t : AssocList.Trie α β) ks
    (h : hasPrefix ks ps = true) :
    (path none ps t).find? ks = t.find? (List.drop ps.length ks) := by
  induction ks generalizing ps
  · match ps with
    | [] => simp [path, find?]
    | _::_ => simp [hasPrefix] at h
  next k v ks ih =>
    match ps with
    | [] => simp [path, find?]
    | _::_ =>
      simp [hasPrefix] at h
      have ⟨h1, h2⟩ := h; clear h
      subst h1
      simp_all [path, find?, AssocList.find?]

theorem path_find_of_not_hasPrefix ps (t : Trie α β) ks
    (h : hasPrefix ks ps = false) :
    (path none ps t).find? ks = none := by
  induction ks generalizing ps
  · match ps with
    | [] => simp [hasPrefix] at h
    | _::_ => simp [path, find?]
  next k v ks ih =>
    match ps with
    | [] => simp [hasPrefix] at h
    | _::_ =>
      simp_all [path, AssocList.find?, find?]
      split <;> try rfl
      split at * <;> try contradiction
      simp_all
      subst_vars
      simp [hasPrefix] at h
      rw [ih _ h]

end Trie
end Trie.AssocList

namespace Trie.CompressedList

/--
Now adding path compression
-/

inductive Trie (α : Type u) (β : Type v) where
  | leaf (val : Option β)
  | path (val : Option β) (ps : List α) (hps : ps ≠ []) (t : Trie α β) : Trie α β
  | node (val : Option β) (c : AssocList α (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .leaf none

def mkPath (ps : List α) (t : Trie α β) : Trie α β :=
  if h : ps = [] then t else .path none ps h t

def insert (t : Trie α β) (ks : List α) (v : β) : Trie α β := match t with
  | .leaf val =>
    if h : ks = [] then
      .leaf (some v)
    else
      .path val ks h (.leaf (some v))
  | .path val ps hps t' =>
    if _h : ks = [] then
      .path (some v) ps hps t'
    else
      let pfx := commonPrefix ks ps
      if hpfx : pfx = [] then
        let c::ks' := ks
        let c'::ps' := ps
        let t := mkPath ks' (.leaf (some v))
        let t'' := mkPath ps' t'
        .node val (.cons c' t'' (.cons c t .nil)) -- order matters for refinement proof!
      else
          -- split common prefix, continue
          .path val pfx hpfx <| insert
            (.mkPath (ps.drop pfx.length) t')
            (ks.drop pfx.length)
            v
    | .node val cs =>
      match ks with
      | [] => .node (some v) cs
      | c::ks => .node val (cs.upsert c fun t? => (t?.getD empty).insert ks v)
termination_by ks.length
decreasing_by
· simp_wf
  rw [← List.length_eq_zero] at hpfx _h
  simp [pfx] at hpfx
  omega
· simp_wf

def find? : (t : Trie α β) → (ks : List α) → Option β
  | .leaf val, [] => val
  | .leaf _, (_::_) => none
  | .path val _ _ _, [] => val
  | .path _ ps _ t', ks@(_::_) =>
    if hasPrefix ks ps then
      t'.find? (ks.drop ps.length)
    else
      none
  | .node val _cs, [] => val
  | .node _val cs, k::ks =>
    match cs.find? k with
    | none => none
    | some t => t.find? ks
termination_by _ ks => ks.length
decreasing_by
· simp_wf
  subst_vars
  cases ps; contradiction;
  simp
  omega
· simp_wf


def uncompress : Trie α β → AssocList.Trie α β
  | .leaf val => .node val .nil
  | .node val cs => .node val (cs.mapSized fun t _ => t.uncompress)
  | .path val ps _ t => .path val ps t.uncompress

@[simp]
theorem uncompress_mkPath (ps : List α) (t : Trie α β) :
    (mkPath ps t).uncompress = .path none ps t.uncompress := by
  cases ps <;> simp [mkPath, AssocList.Trie.path, uncompress]


@[simp]
theorem empty_spec : (empty : Trie α β).uncompress = .empty := by rfl

theorem insert_spec (t : Trie α β) (ks : List α) (v : β) :
    (insert t ks v).uncompress = t.uncompress.insert ks v := by
  -- Bug in functional induction!
  -- induction t, ks, v using insert.induct
  unfold insert
  split
  next t val =>
    cases ks
    next =>
      simp [uncompress, AssocList.Trie.insert]
    next k ks =>
      simp [uncompress, AssocList.Trie.insert, AssocList.Trie.path, AssocList.upsert,
        AssocList.Trie.path_eq_insert]
  next ps _ t'=>
    match ks with
    | [] =>
      cases ps; contradiction
      simp [uncompress, AssocList.Trie.path, AssocList.Trie.insert]
    | (k::ks) =>
      have p::ps := ps
      simp only [↓reduceDite, ne_eq]
      match hpfx : commonPrefix (k::ks) (p::ps) with
      | [] =>
        simp only [↓reduceDite]
        simp [commonPrefix] at hpfx
        simp [uncompress, AssocList.Trie.path, AssocList.Trie.insert, AssocList.mapSized,
          AssocList.upsert, hpfx]
      | p1::ps =>
        simp [uncompress, AssocList.Trie.insert, AssocList.Trie.path]
        simp [commonPrefix] at hpfx
        split at hpfx <;> try contradiction
        simp at hpfx
        cases hpfx
        subst p k ps
        rw [insert_spec]
        simp [AssocList.upsert, uncompress]
        rw [← AssocList.Trie.path_insert_eq_commonPrefix]
  next t val cs =>
    match ks with
    | [] => simp [uncompress, AssocList.Trie.insert]
    | (k::ks) =>
      simp [uncompress, AssocList.Trie.insert]
      apply AssocList.mapVal_upsert_congr
      intro t?
      rw [insert_spec]
      match t? with
      | none => simp
      | some t' => simp
termination_by ks.length

theorem find?_spec (t : Trie α β) (ks : List α):
    t.uncompress.find? ks = t.find? ks := by
  induction t, ks using find?.induct
  all_goals solve
    | simp [uncompress, find?, AssocList.Trie.find?, AssocList.find?, *]
  next ps _ _ _ _ hpfx _ =>
    have p::ps := ps
    simp [hasPrefix] at hpfx
    cases hpfx with | _ heq hpfx =>
    subst p
    simp_all [uncompress, find?, AssocList.Trie.find?, AssocList.find?, hasPrefix,
      AssocList.Trie.path_find_of_hasPrefix]
  next ps _ _ _ _ hpfx =>
    have p::ps := ps
    simp_all [uncompress, find?, AssocList.Trie.find?, AssocList.find?, hasPrefix,
      AssocList.Trie.path_find_of_hasPrefix]
    split
    · simp
    next h =>
      split at h <;> simp at h
      subst h
      rw [AssocList.Trie.path_find_of_not_hasPrefix]
      apply hpfx
      simp_all

theorem find?_empty (k : List α) : find? (empty : Trie α β) k = none := by
  simp [← find?_spec, Trie.AssocList.Trie.find?_empty, empty_spec]

theorem find?_insert_eq (t : Trie α β) (k : List α) (v : β) :
    (t.insert k v).find? k = some v := by
  simpa [insert_spec, ← find?_spec] using Trie.AssocList.Trie.find?_insert_eq _ _ _

theorem find?_insert_neq (t : Trie α β) (k k' : List α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  simpa [insert_spec, ← find?_spec] using Trie.AssocList.Trie.find?_insert_neq _ _ _ hne _

end Trie
end Trie.CompressedList


section ArrayLib

theorem Array.drop_data_cons {α : Type _} (as : Array α) (i : Nat) (h : i < as.size) :
  as.data.drop i = as[i] :: as.data.drop (i + 1) := by sorry

theorem Array.drop_data_nil {α : Type _} (as : Array α) (i : Nat) (h : ¬ i < as.size) :
  as.data.drop i = [] := by sorry

@[simp]
theorem Array.extract_data {α} (as : Array α) (i : Nat) (j : Nat) :
  (as.extract i j).data = (as.data.take j).drop i := by sorry

theorem Array.modify_data {α} (as : Array α) (i : Nat) (f : α → α) (h : i < as.size):
    (Array.modify as i f).data = as.data.take i ++ [f as[i]] ++ as.data.drop (i + 1) := by sorry

theorem Array.data_getElem {α} (as : Array α) (i : Nat) (h : i < as.size) :
  as.data[i] = as[i] := rfl

theorem Array.size_extract {α} (as : Array α) (start stop : Nat) :
    Array.size (Array.extract as start stop) = min stop (Array.size as) - start :=
  by sorry

theorem Array.get_extract {α} {i : Nat} {as : Array α} {start stop : Nat} (h : i < Array.size (Array.extract as start stop)) :
 (Array.extract as start stop)[i] = as[start + i]'(by simp [Array.size_extract] at *; omega) := sorry

def Array.attach {α} (as : Array α) : Array {x : α // x ∈ as} := by sorry

@[simp]
theorem Array.attach_singleton {α} (a : α) : #[a].attach = #[⟨a, .mk (by simp)⟩] := sorry

@[simp]
theorem Array.map_attach {α β} (xs : Array α) (f : α → β) :
  xs.attach.map (fun ⟨x, _⟩ => f x) = xs.map f := sorry

@[simp]
theorem Array.map_toArray {α β} (xs : List α) (f : α → β) :
  xs.toArray.map f = (xs.map f).toArray := sorry

@[simp]
theorem Array.map_two {α β} (x₁ x₂ : α) (f : α → β) :
  #[x₁, x₂].map f = #[f x₁, f x₂] := sorry

@[simp]
theorem List.drop_drop :
  ∀ (n m : Nat) (l : List α), List.drop n (List.drop m l) = List.drop (n + m) l :=
  by sorry

-- TODO: Lemma has wrong name in std
axiom Array.getElem_mem :
  ∀ {α : Type u} {i : Nat} (a : Array α) (h : i < Array.size a), a[i] ∈ a

theorem List.length_take_of_le :
  ∀ {n : Nat} {l : List α}, n ≤ l.length → (List.take n l).length = n := by sorry

theorem List.drop_cons {α : Type _} (as : List α) (i : Nat) (h : i < as.length) :
  as.drop i = as[i] :: as.drop (i + 1) := by sorry

theorem List.drop_nil_of_length {α : Type _} (as : List α) (i : Nat) (h : ¬ (i < as.length)) :
  as.drop i = [] := by sorry

end ArrayLib

namespace AssocArray

def upsert (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) : Array α × Array β :=
  go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          (ks, vs.modify i (fun v => f (some v)))
        else
          go (i + 1)
      else
        ((ks.extract 0 i).push k, vs.push (f none))
    else
      (ks.push k, (vs.extract 0 i).push (f none))
  termination_by ks.size - i

def toAssocList (kvs : Array α × Array β) : AssocList α β :=
  go kvs.1.data kvs.2.data
where
  go | (k::ks), (v::vs) => .cons k v (go ks vs)
     | _, _ => .nil

@[simp]
theorem toAssocList_go_map {γ} (ks : List α) (vs : List β) (f : β → γ) :
   toAssocList.go ks (vs.map f) = AssocList.mapVal f (toAssocList.go ks vs) := by
  induction ks generalizing vs
  · cases vs <;> simp [toAssocList.go, AssocList.mapVal, *]
  · cases vs <;> simp [toAssocList.go, AssocList.mapVal, *]

@[simp]
theorem toAssocList_map {γ} (ks : Array α) (vs : Array β) (f : β → γ) :
    toAssocList (ks, vs.map f) = AssocList.mapVal f (toAssocList (ks, vs)) := by
  simp [toAssocList, toAssocList_go_map]

def upsert_go_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) (i : Nat) :
    toAssocList (upsert.go ks vs k f i) =
      (toAssocList.go (ks.data.drop i) (vs.data.drop i)).upsert k f := by
  sorry

def upsert_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) :
    toAssocList (upsert ks vs k f) = (toAssocList.go ks.data vs.data).upsert k f := by
  simp [upsert, upsert_go_spec]

def find?' (ks : Array α) (vs : Array β) (k : α) : Option {x : β // x ∈ vs} := go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          some ⟨vs[i], Array.getElem_mem _ hj⟩
        else
          go (i + 1)
      else
        none
    else
      none
  termination_by ks.size - i

def find? (ks : Array α) (vs : Array β) (k : α) : Option β := (find?' ks vs k).map (·.val)

def find?_spec (ks : Array α) (vs : Array β) (k : α) :
    (find? ks vs k) = (toAssocList.go ks.data vs.data).find? k := by
  sorry

end AssocArray

namespace Trie.Array

/--
Now additing path compression.
-/
inductive Trie (α : Type u) (β : Type v) where
  | leaf (val : Option β)
  | path (val : Option β) (ps : Array α) (hps : 0 < ps.size) (t : Trie α β) : Trie α β
  | node (val : Option β) (ks : Array α) (vs : Array (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .leaf none

def commonPrefix (xs : Array α) (ys : Array α) (offset1 : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if h : offset1 + i < xs.size then
      if h' : i < ys.size then
        if xs[offset1 + i] = ys[i] then
          loop (i + 1)
        else
          i
      else
        i
    else
      i
    termination_by ys.size - i
  loop 0

def hasPrefix (xs : Array α) (ys : Array α) (offset1 : Nat) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h' : i < ys.size then
      if h : offset1 + i < xs.size then
        if xs[offset1 + i] = ys[i] then
          loop (i + 1)
        else
          false
      else
        false
    else
      true
    termination_by ys.size - i
  loop 0


theorem commonPrefix_spec (ks ps : Array α) (i : Nat) :
  _root_.commonPrefix (ks.data.drop i) ps.data = ps.data.take (commonPrefix ks ps i) :=
  sorry

def mkPath (ps : Array α) (t : Trie α β) : Trie α β :=
  if h : 0 < ps.size  then .path none ps h t else t

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go 0 t where
  go (i : Nat)
    | .leaf val =>
      if h : i < ks.size then
        path val (ks.extract i ks.size) (by simp [Array.size_extract]; omega) (.leaf (some v))
      else
        .leaf (some v)
    | .path val ps hps t' =>
      if h : i < ks.size then
        let j := commonPrefix ks ps i
        if hj : 0 < j then
          -- split common prefix, continue
          .path val (ps.extract 0 j) (by simp [Array.size_extract];omega) <| go (i + j) <|
              .mkPath (ps.extract j ps.size) t'
        else
          -- no common prefix, split off first key
          let c := ks[i]
          let c' := ps[0]'(by omega)
          let t := mkPath (ks.extract (i+1) ks.size) (.leaf (some v))
          let t'' := mkPath (ps.extract 1 ps.size) t'
          .node val #[c', c] #[t'', t] -- order matters for refinemnet proof!
      else
        .path (some v) ps hps t'
    | .node val ks' vs =>
      if h : i < ks.size then
        let (ks'', vs'') := AssocArray.upsert ks' vs ks[i] fun t? =>
          go (i + 1) (t?.getD empty)
        .node val ks'' vs''
      else
        .node (some v) ks' vs
  termination_by ks.size - i
  decreasing_by all_goals simp_wf; omega

def find? (t : Trie α β) (ks : Array α) : Option β := go 0 t where
  go
    | i, .leaf val =>
      if i < ks.size then
        none
      else
        val
    | i, path val ps _ t' =>
      if i < ks.size then
        if hasPrefix ks ps i then
          go (i + ps.size) t'
        else
          none
      else
        val
    | i, .node val ks' vs =>
      if h : i < ks.size then
        match AssocArray.find? ks' vs ks[i] with
        | none => none
        | some t => go (i + 1) t
      else
        val
  termination_by i => ks.size - i
  decreasing_by all_goals simp_wf; omega

def abstract : Trie α β → CompressedList.Trie α β
  | .leaf val => .leaf val
  | .path val ps hps t => .path val ps.data (by sorry) t.abstract
  | .node val ks vs => .node val (AssocArray.toAssocList (ks, vs.attach.map fun ⟨t,_⟩ => t.abstract))

@[simp]
theorem empty_spec :
    (empty : Trie α β).abstract = .empty := by
  simp [abstract, empty, Trie.Abstract.Trie.empty]
  rfl

theorem mkPath_spec (ks : Array α) (t : Trie α β) :
    (mkPath ks t).abstract = CompressedList.Trie.mkPath ks.data t.abstract := by
  sorry

theorem has_prefix_loop_spec (ks ps : Array α) (o : Nat) (i : Nat ):
    hasPrefix.loop ks ps o i = _root_.hasPrefix (ks.data.drop (o + i)) (ps.data.drop i) := by
  induction i using hasPrefix.loop.induct ks ps o
  · rw [hasPrefix.loop]
    rw [Array.drop_data_cons ks (o + _) ‹_›]
    rw [Array.drop_data_cons ps _ ‹_›]
    simp [*, _root_.hasPrefix, Nat.add_assoc]
  · rw [hasPrefix.loop]
    rw [Array.drop_data_cons ks (o + _) ‹_›]
    rw [Array.drop_data_cons ps _ ‹_›]
    simp [*, _root_.hasPrefix, Nat.add_assoc]
  · rw [hasPrefix.loop]
    rw [Array.drop_data_nil ks (o + _) ‹_›]
    rw [Array.drop_data_cons ps _ ‹_›]
    simp [*, _root_.hasPrefix, Nat.add_assoc]
  · rw [hasPrefix.loop]
    rw [Array.drop_data_nil ps _ ‹_›]
    simp [*, _root_.hasPrefix, Nat.add_assoc]

theorem has_prefix_spec (ks ps : Array α) (i : Nat) :
    hasPrefix ks ps i = _root_.hasPrefix (ks.data.drop i) ps.data := by
  apply has_prefix_loop_spec


theorem find?_go_spec (t : Trie α β)  (ks : Array α) (i : Nat) :
    find?.go ks i t = t.abstract.find? (ks.data.drop i) := by
  induction i, t using find?.go.induct ks
  next i val h =>
    rw [Array.drop_data_cons ks i h]
    simp_all [find?.go, abstract, CompressedList.Trie.find?]
  next i val h =>
    rw [Array.drop_data_nil ks i h]
    simp_all only [find?.go, abstract, CompressedList.Trie.find?, if_false]
  next i val ps hps t' h hpfx ih =>
    rw [Array.drop_data_cons ks i h]
    simp_all only [find?.go, abstract, CompressedList.Trie.find?, if_true]
    rw [if_pos]
    case hc => rw [has_prefix_spec, Array.drop_data_cons ks i h] at hpfx; exact hpfx
    rw [← Array.drop_data_cons ks i h]
    congr 1
    simp [Array.size, Nat.add_comm]
  next i val ps hps t' h hpfx =>
    rw [Array.drop_data_cons ks i h]
    simp_all only [find?.go, abstract, CompressedList.Trie.find?, if_true, if_false]
    rw [if_neg]
    case hnc => rw [has_prefix_spec, Array.drop_data_cons ks i h] at hpfx; exact hpfx
  next i val ps hps t' h =>
    rw [Array.drop_data_nil ks i h]
    simp_all only [find?.go, abstract, CompressedList.Trie.find?, if_true, if_false]
  next i val ks' s h x =>
    rw [Array.drop_data_cons ks i h]
    simp_all [find?.go, abstract, CompressedList.Trie.find?, dite_true, AssocArray.find?_spec,
      Array.map_attach, AssocArray.toAssocList, AssocArray.toAssocList_go_map]
  next i val ks' vs h t x ih =>
    rw [Array.drop_data_cons ks i h]
    simp_all [find?.go, abstract, CompressedList.Trie.find?, dite_true, AssocArray.find?_spec,
      Array.map_attach, AssocArray.toAssocList, AssocArray.toAssocList_go_map]
  next i val ks' vs h =>
    rw [Array.drop_data_nil ks i h]
    simp_all only [find?.go, abstract, CompressedList.Trie.find?]
    apply dite_false -- why is the simplifier so confused here?

theorem find?_spec (t : Trie α β)  (ks : Array α)  :
    t.find? ks = t.abstract.find? ks.data := by
  simp [find?, find?_go_spec]


theorem commonPrefix_le_length (ks ps : Array α) (i : Nat) :
    commonPrefix ks ps i ≤ ps.data.length := by
  sorry

theorem insert_go_spec (t : Trie α β) (ks : Array α) (v : β) (i : Nat) :
    (insert.go ks v i t).abstract = t.abstract.insert (ks.data.drop i) v := by
  induction i, t using insert.go.induct ks v
  next i val h =>
    simp_all [insert.go, abstract, CompressedList.Trie.insert, List.drop_cons]
  next i val h =>
    simp_all [insert.go, abstract, CompressedList.Trie.insert, List.drop_nil_of_length, -Nat.not_lt]
  next i val ps hps t' hi j hj ih =>
    simp_all [insert.go, abstract, CompressedList.Trie.insert, mkPath_spec]
    rw [dif_neg]
    case hnc => simp [List.drop_cons, *]
    rw [dif_neg]
    case hnc =>
      rw [commonPrefix_spec]
      unfold Array.size at hps
      simp [j] at hj
      revert hps hj
      cases ps.data <;> cases commonPrefix ks ps i <;> intro _ _ <;> simp_all
    simp [commonPrefix_spec, List.length_take_of_le (commonPrefix_le_length ..), j, Nat.add_comm]
  next i val ps hps t' hi j hj =>
    simp [insert.go, *, abstract, CompressedList.Trie.insert, mkPath_spec, AssocArray.toAssocList,
      AssocArray.toAssocList.go]
    rw [dif_neg]
    case hnc => simp [Array.drop_data_cons, *]
    rw [dif_pos]
    case hc =>
      rw [commonPrefix_spec]
      unfold Array.size at hps
      simp [j] at hj
      revert hps hj
      cases ps.data <;> cases commonPrefix ks ps i <;> intro _ _ <;> simp_all
    split
    split
    rw [Array.drop_data_cons ks i ‹_›] at *
    rename_i h _
    simp_all [Array.getElem_eq_data_get, h]
    have ⟨ps⟩ := ps
    simp at h
    subst h
    rfl
  next i val ps hps t' h =>
    simp [insert.go, *, abstract, CompressedList.Trie.insert, mkPath_spec, AssocArray.toAssocList,
      AssocArray.toAssocList.go]
    rw [dif_pos]
    case hc => simp [Array.drop_data_nil, *]
  next i val ks' vs h ks'' vs'' x ih =>
    rw [Array.drop_data_cons ks i h]
    simp [insert.go, *, abstract, CompressedList.Trie.insert, mkPath_spec, AssocArray.toAssocList,
      AssocArray.toAssocList.go]
    rw [← AssocArray.toAssocList.eq_1 (ks'', vs''), ← x]; clear x
    rw [AssocArray.upsert_spec]
    apply AssocList.mapVal_upsert_congr
    intro t?
    rw [ih]
    cases t? <;> simp
  next i val ks' vs h =>
    rw [Array.drop_data_nil ks i h]
    simp [insert.go, *, abstract, CompressedList.Trie.insert, mkPath_spec, AssocArray.toAssocList,
      AssocArray.toAssocList.go]

theorem insert_spec (t : Trie α β) (ks : Array α) (v : β) :
    (t.insert ks v).abstract = t.abstract.insert ks.data v := by
  simp [insert, insert_go_spec]

theorem find?_empty (k : Array α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, Trie.CompressedList.Trie.find?_empty, empty_spec]

theorem find?_insert_eq (t : Trie α β) (k : Array α) (v : β) :
    (t.insert k v).find? k = some v := by
  simpa [insert_spec, find?_spec] using Trie.CompressedList.Trie.find?_insert_eq _ _ _

theorem find?_insert_neq (t : Trie α β) (k k' : Array α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  have : k.data ≠ k'.data := by cases k; cases k'; simpa using hne
  simpa [insert_spec, find?_spec] using
    Trie.CompressedList.Trie.find?_insert_neq _ _ _ this _

end Trie
end Trie.Array
