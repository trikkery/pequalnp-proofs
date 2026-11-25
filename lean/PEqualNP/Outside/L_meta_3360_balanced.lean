import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3360_balanced

def edge (a : Nat) : Bool :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
    a.testBit (e / 10) && a.testBit (e % 10)

def signature (u a : Nat) : List Bool :=
  edge a :: (((List.range 9).filter fun i => !(u.testBit i)).map fun i => edge (a ||| (1 <<< i)))

def verifyBlock (u : Nat) (data : Nat × Bool × List Nat) : Bool :=
  let k := data.1
  let chain := data.2.1
  let rows := data.2.2
  (rows.all fun a => (a &&& u) == a) &&
    if chain then
      decide (k + 1 ≤ rows.length) &&
        (rows.zip (rows.drop 1)).all fun pair =>
          ((pair.1 &&& pair.2) == pair.1) && (signature u pair.1 != signature u pair.2)
    else
      decide (2 ^ (k - 1) < ((rows.map (signature u)).eraseDups.length))

abbrev Record := Nat × (Nat × Bool × List Nat) × (Nat × Bool × List Nat)

def verifyRecord (r : Record) : Bool :=
  verifyBlock r.1 r.2.1 && verifyBlock (511 - r.1) r.2.2

def lower (r : Record) : Nat := r.2.1.1 + r.2.2.1

def chunk0 : List Record :=
  [(15, (4, false, [0,1,2,3,4,5,8,9,10]), (4, true, [0,256,384,400,464])),
   (23, (3, true, [0,16,20,22]), (4, true, [0,128,192,200,456])),
   (27, (3, true, [0,8,10,26]), (4, true, [0,64,96,100,356])),
   (29, (3, true, [0,8,9,25]), (4, true, [0,256,384,386,450])),
   (30, (3, true, [0,16,20,28]), (4, true, [0,256,384,385,449])),
   (39, (4, false, [0,1,2,3,4,5,32,34,36]), (4, true, [0,256,384,400,464])),
   (43, (4, true, [0,32,40,42,43]), (4, true, [0,128,384,400,464])),
   (45, (4, false, [0,1,4,5,8,9,12,32,36]), (4, true, [0,256,384,400,464])),
   (46, (4, true, [0,32,40,42,46]), (4, true, [0,16,272,400,464])),
   (51, (4, true, [0,32,48,50,51]), (4, true, [0,128,192,200,456])),
   (53, (4, true, [0,32,48,52,53]), (4, true, [0,256,384,386,450])),
   (54, (4, true, [0,16,20,52,54]), (4, true, [0,128,192,200,456]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk0_verified : chunk0.all verifyRecord = true := by decide

def chunk1 : List Record :=
  [(57, (3, true, [0,32,40,56]), (4, true, [0,128,384,386,450])),
   (58, (4, true, [0,16,48,50,58]), (4, true, [0,128,384,385,449])),
   (60, (4, true, [0,16,48,52,60]), (4, true, [0,2,130,386,450])),
   (71, (4, true, [0,64,68,69,71]), (4, true, [0,256,384,400,432])),
   (75, (4, true, [0,64,72,73,75]), (4, true, [0,256,272,276,404])),
   (77, (4, true, [0,64,72,73,77]), (4, true, [0,256,384,400,432])),
   (78, (3, true, [0,64,72,76]), (4, true, [0,16,272,400,432])),
   (83, (4, false, [0,1,2,3,16,18,64,65,80]), (4, false, [0,4,8,12,32,36,40,256,260])),
   (85, (4, true, [0,64,80,84,85]), (4, true, [0,256,384,386,418])),
   (86, (4, true, [0,64,80,84,86]), (4, true, [0,256,384,385,417])),
   (89, (4, true, [0,64,72,73,89]), (3, true, [0,4,260,388])),
   (90, (3, true, [0,64,80,88]), (4, true, [0,256,260,261,389]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk1_verified : chunk1.all verifyRecord = true := by decide

def chunk2 : List Record :=
  [(92, (4, true, [0,64,80,84,92]), (4, true, [0,128,130,386,418])),
   (99, (3, true, [0,64,96,98]), (4, true, [0,128,384,400,408])),
   (101, (4, true, [0,64,96,100,101]), (4, true, [0,256,384,400,408])),
   (102, (4, true, [0,64,96,100,102]), (4, true, [0,256,384,385,401])),
   (105, (4, true, [0,64,96,104,105]), (4, true, [0,128,384,400,404])),
   (106, (4, true, [0,64,96,104,106]), (4, true, [0,128,144,400,404])),
   (108, (4, true, [0,64,96,104,108]), (4, true, [0,16,272,400,403])),
   (113, (4, true, [0,64,96,112,113]), (4, true, [0,128,384,386,394])),
   (114, (4, true, [0,64,96,112,114]), (4, true, [0,128,384,385,393])),
   (116, (4, false, [0,4,16,20,32,36,48,64,68]), (4, true, [0,128,136,138,394])),
   (120, (4, true, [0,64,80,112,120]), (4, true, [0,128,130,386,390])),
   (135, (3, true, [0,128,130,134]), (4, true, [0,64,80,112,368]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk2_verified : chunk2.all verifyRecord = true := by decide

def chunk3 : List Record :=
  [(139, (4, true, [0,128,136,138,139]), (4, true, [0,64,96,112,368])),
   (141, (4, true, [0,128,136,137,141]), (4, true, [0,256,272,274,338])),
   (142, (4, true, [0,128,136,138,142]), (4, true, [0,64,96,112,368])),
   (147, (4, true, [0,128,144,146,147]), (4, true, [0,64,96,104,360])),
   (149, (3, true, [0,128,144,148]), (4, true, [0,32,34,42,298])),
   (150, (4, true, [0,128,144,146,150]), (4, true, [0,64,96,104,360])),
   (153, (4, true, [0,128,136,137,153]), (3, true, [0,256,260,324])),
   (154, (4, true, [0,128,144,146,154]), (4, true, [0,64,96,100,356])),
   (156, (4, false, [0,4,8,12,16,20,128,136,144]), (4, false, [0,1,2,3,32,34,256,257,258])),
   (163, (3, true, [0,128,130,162]), (4, true, [0,256,272,276,340])),
   (165, (3, true, [0,32,36,164]), (4, true, [0,256,272,274,338])),
   (166, (3, true, [0,32,36,164]), (4, true, [0,64,72,73,329]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk3_verified : chunk3.all verifyRecord = true := by decide

def chunk4 : List Record :=
  [(169, (4, true, [0,128,136,137,169]), (4, true, [0,256,272,276,340])),
   (170, (4, true, [0,128,136,138,170]), (4, true, [0,16,272,276,340])),
   (172, (3, true, [0,32,40,168]), (4, true, [0,16,272,274,338])),
   (177, (4, false, [0,1,16,17,32,48,128,129,144]), (4, false, [0,2,4,6,8,10,256,258,260])),
   (178, (4, true, [0,128,144,146,178]), (4, true, [0,64,72,73,329])),
   (180, (4, true, [0,32,48,52,180]), (3, true, [0,256,258,322])),
   (184, (3, true, [0,128,144,176]), (4, true, [0,256,260,261,325])),
   (195, (4, true, [0,128,192,193,195]), (4, true, [0,256,272,276,308])),
   (197, (4, true, [0,128,192,193,197]), (4, true, [0,256,272,274,306])),
   (198, (4, false, [0,2,4,6,64,68,128,130,192]), (4, false, [0,1,8,9,17,32,40,256,257])),
   (201, (4, false, [0,1,8,9,64,65,72,128,129]), (4, true, [0,256,272,276,308])),
   (202, (4, true, [0,128,192,200,202]), (4, true, [0,16,272,276,308]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk4_verified : chunk4.all verifyRecord = true := by decide

def chunk5 : List Record :=
  [(204, (4, true, [0,128,192,200,204]), (4, true, [0,16,272,274,306])),
   (209, (4, true, [0,128,192,208,209]), (4, true, [0,32,40,42,298])),
   (210, (4, true, [0,128,192,208,210]), (4, true, [0,256,260,261,293])),
   (212, (4, true, [0,128,192,208,212]), (4, true, [0,32,40,42,298])),
   (216, (4, true, [0,128,192,208,216]), (4, true, [0,256,260,261,293])),
   (225, (4, true, [0,128,192,193,225]), (4, true, [0,256,272,276,284])),
   (226, (3, true, [0,128,192,224]), (4, true, [0,256,257,261,277])),
   (228, (4, true, [0,64,96,100,228]), (3, true, [0,256,274,282])),
   (232, (4, true, [0,128,192,200,232]), (4, true, [0,16,272,276,278])),
   (240, (4, true, [0,128,192,208,240]), (4, true, [0,256,260,261,269])),
   (263, (4, true, [0,256,260,261,263]), (4, true, [0,128,192,208,240])),
   (267, (4, false, [0,1,2,3,8,9,10,256,257]), (4, true, [0,64,96,112,240]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk5_verified : chunk5.all verifyRecord = true := by decide

def chunk6 : List Record :=
  [(269, (4, true, [0,256,260,261,269]), (4, true, [0,128,192,208,240])),
   (270, (4, false, [0,2,4,6,8,10,256,258,260]), (4, true, [0,128,192,208,240])),
   (275, (4, true, [0,16,272,274,275]), (4, true, [0,64,96,104,232])),
   (277, (4, true, [0,16,272,276,277]), (4, true, [0,128,192,200,232])),
   (278, (4, true, [0,256,272,276,278]), (4, true, [0,128,192,200,232])),
   (281, (3, true, [0,256,257,273]), (4, true, [0,64,96,100,228])),
   (282, (4, true, [0,256,272,274,282]), (4, true, [0,32,96,100,228])),
   (284, (4, true, [0,256,272,276,284]), (4, true, [0,128,192,193,225])),
   (291, (4, false, [0,1,2,3,32,34,256,257,258]), (4, true, [0,128,192,208,216])),
   (293, (4, true, [0,256,260,261,293]), (4, true, [0,128,192,208,216])),
   (294, (4, false, [0,2,4,6,32,34,36,256,258]), (4, true, [0,128,136,200,216])),
   (297, (4, false, [0,1,8,9,32,33,40,256,257]), (4, true, [0,128,192,208,212]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk6_verified : chunk6.all verifyRecord = true := by decide

def chunk7 : List Record :=
  [(298, (4, true, [0,32,40,42,298]), (4, true, [0,128,192,208,212])),
   (300, (4, false, [0,4,8,12,32,36,40,256,260]), (4, true, [0,128,192,208,210])),
   (305, (3, true, [0,16,272,304]), (4, true, [0,128,192,200,204])),
   (306, (4, true, [0,256,272,274,306]), (4, true, [0,128,192,200,204])),
   (308, (4, true, [0,256,272,276,308]), (4, true, [0,128,192,200,202])),
   (312, (3, true, [0,256,272,304]), (4, true, [0,128,192,193,197])),
   (323, (3, true, [0,256,258,322]), (4, true, [0,16,48,52,180])),
   (325, (4, true, [0,256,260,261,325]), (4, true, [0,128,144,146,178])),
   (326, (3, true, [0,256,260,324]), (4, true, [0,128,136,137,169])),
   (329, (4, true, [0,64,72,73,329]), (4, true, [0,4,20,52,180])),
   (330, (3, true, [0,256,258,322]), (4, true, [0,32,48,52,180])),
   (332, (3, true, [0,64,72,328]), (4, true, [0,128,144,146,178]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk7_verified : chunk7.all verifyRecord = true := by decide

def chunk8 : List Record :=
  [(337, (3, true, [0,16,272,336]), (4, true, [0,32,40,42,170])),
   (338, (4, true, [0,256,272,274,338]), (3, true, [0,32,40,168])),
   (340, (4, true, [0,256,272,276,340]), (4, true, [0,128,136,138,170])),
   (344, (4, false, [0,8,16,24,64,72,80,256,272]), (4, false, [0,1,2,3,4,5,32,34,36])),
   (353, (3, true, [0,64,96,352]), (4, true, [0,128,144,146,154])),
   (354, (3, true, [0,256,258,322]), (4, true, [0,128,136,137,153])),
   (356, (4, true, [0,64,96,100,356]), (4, true, [0,128,136,138,154])),
   (360, (4, true, [0,64,96,104,360]), (4, true, [0,128,144,146,150])),
   (368, (4, true, [0,64,96,112,368]), (4, true, [0,128,136,138,142])),
   (387, (4, true, [0,128,130,386,387]), (4, true, [0,64,80,112,120])),
   (389, (4, true, [0,128,384,385,389]), (4, true, [0,64,80,112,120])),
   (390, (4, true, [0,128,384,386,390]), (4, true, [0,64,96,104,120]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk8_verified : chunk8.all verifyRecord = true := by decide

def chunk9 : List Record :=
  [(393, (4, true, [0,256,384,385,393]), (4, true, [0,64,96,112,118])),
   (394, (4, true, [0,256,384,386,394]), (4, true, [0,64,96,112,117])),
   (396, (3, true, [0,128,384,392]), (4, true, [0,64,96,112,114])),
   (401, (4, true, [0,16,272,400,401]), (4, true, [0,64,96,104,108])),
   (402, (4, false, [0,2,16,18,128,130,144,146,256]), (4, true, [0,64,96,104,108])),
   (404, (4, true, [0,128,384,400,404]), (4, true, [0,64,96,104,106])),
   (408, (4, true, [0,256,384,400,408]), (4, true, [0,64,96,100,102])),
   (417, (4, true, [0,256,384,385,417]), (4, true, [0,64,80,84,92])),
   (418, (4, true, [0,256,384,386,418]), (4, true, [0,8,72,73,89])),
   (420, (3, true, [0,256,260,388]), (4, true, [0,64,72,73,89])),
   (424, (3, true, [0,256,384,416]), (4, true, [0,64,80,84,86])),
   (432, (4, true, [0,256,384,400,432]), (4, true, [0,64,72,73,77]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk9_verified : chunk9.all verifyRecord = true := by decide

def chunk10 : List Record :=
  [(449, (4, true, [0,256,384,385,449]), (4, true, [0,16,20,52,60])),
   (450, (4, true, [0,256,384,386,450]), (3, true, [0,8,40,56])),
   (452, (3, true, [0,128,384,448]), (4, true, [0,32,40,42,58])),
   (456, (4, true, [0,128,192,200,456]), (4, true, [0,16,20,52,54])),
   (464, (4, true, [0,256,384,400,464]), (4, true, [0,32,40,42,46])),
   (480, (4, false, [0,32,64,96,128,160,192,256,384]), (4, false, [0,1,2,3,4,5,8,9,10]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk10_verified : chunk10.all verifyRecord = true := by decide

def records : List Record := chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10

def fourMasks : List Nat :=
  (List.range 512).filter fun u => ((List.range 9).filter u.testBit).length == 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem balancedCertificate :
    records.map Prod.fst = fourMasks ∧ records.all verifyRecord = true ∧
      (records.map lower).count 7 = 36 ∧ (records.map lower).count 8 = 90 ∧
      records.all (fun r => decide (7 ≤ lower r)) = true := by
  refine ⟨by decide, ?_, by decide, by decide, by decide⟩
  simp only [records, List.all_append, chunk0_verified, chunk1_verified, chunk2_verified, chunk3_verified, chunk4_verified, chunk5_verified, chunk6_verified, chunk7_verified, chunk8_verified, chunk9_verified, chunk10_verified, Bool.and_self]

end PEqualNP.Outside.L_meta_3360_balanced


theorem PEqualNP.Outside.L_meta_3360_balanced :
  let edge (a : Nat) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
      a.testBit (e / 10) && a.testBit (e % 10)
  let signature (u a : Nat) : List Bool :=
    edge a :: (((List.range 9).filter fun i => !(u.testBit i)).map fun i => edge (a ||| (1 <<< i)))
  let verifyBlock (u : Nat) (data : Nat × Bool × List Nat) : Bool :=
    let k := data.1
    let chain := data.2.1
    let rows := data.2.2
    (rows.all fun a => (a &&& u) == a) &&
      if chain then
        decide (k + 1 ≤ rows.length) &&
          (rows.zip (rows.drop 1)).all fun pair =>
            ((pair.1 &&& pair.2) == pair.1) && (signature u pair.1 != signature u pair.2)
      else
        decide (2 ^ (k - 1) < ((rows.map (signature u)).eraseDups.length))
  let Record := Nat × (Nat × Bool × List Nat) × (Nat × Bool × List Nat)
  let verifyRecord (r : Record) : Bool :=
    verifyBlock r.1 r.2.1 && verifyBlock (511 - r.1) r.2.2
  let lower (r : Record) : Nat := r.2.1.1 + r.2.2.1
  
  let fourMasks : List Nat :=
    (List.range 512).filter fun u => ((List.range 9).filter u.testBit).length == 4
  ∃ records : List Record,
    records.map Prod.fst = fourMasks ∧ records.all verifyRecord = true ∧
        (records.map lower).count 7 = 36 ∧ (records.map lower).count 8 = 90 ∧
        records.all (fun r => decide (7 ≤ lower r)) = true := by
  exact ⟨PEqualNP.Outside.L_meta_3360_balanced.records, PEqualNP.Outside.L_meta_3360_balanced.balancedCertificate⟩
