Reverzibilis Szórási Áramlás (**RSF**)

A Reverzibilis Szórási Áramlás (**RSF**) egy gyökérszintű neurális architektúra, amely egy invertálható csatolás primitív köré épül, nem pedig perceptronokra, konvolúciókra, rekurzióra vagy figyelemre (attention). Az egész modell egyetlen bijektív művelet köré szerveződik, amely kettéválasztja az állapotot, affinnal, exponenciált skálával és eltolással transzformál, és minden rétegben formális invertálhatóságot garantál.

Az **RSF** az alábbiakat tartalmazza:

- Egy formálisan verifikált mag (Twelf/Beluga stílusú bizonyítások az invertálhatóságra, alakbiztonságra, regiszterbiztonságra és rendszerszintű invariánsokra).
- Nagy teljesítményű **GPU**-implementáció Futhark kernelekkel és Zig kötésekkel, **NVIDIA** **GPU**-kat célozva.
- Egy kicsi, önálló C/Zig/Futhark backend, amely bedobható építőelemként szolgálhat kutatási modellekhez vagy produkciós rendszerekhez.

---

 Kulcsötletek

Az **RSF** középpontjában egyetlen, irreducibilis művelet áll egy [x1, x2] vektoron, egyenlő felekkel:

## Felosztás: a vektort két félre bontjuk: x1 és x2.

## Skála számítása a második félből:

scale = exp(clip(W_s  x2 + b_s))

## Eltolás számítása a skálázott első félből:

trans = W_t  y1 + b_t

## Csatolás alkalmazása:

y1 = x1  scale y2 = x2 + trans

Mind az előremenő, mind az inverz irány implementálva van és formálisan bizonyított, hogy egymás kölcsönös inverzei (rsf-full-invertibility, rsf-invertible-single, rsf-multi-invertibility).

A teljes modell ezeket a csatolási rétegeket tanulható permutációkkal (rsfscatter) egymásra stackeli. Nincs attention, nincs konvolúció, nincs rekurzív cella és nincs klasszikus **MLP** blokk az **RSF** architektúra magjában — maga a csatolás az elsődleges számítási primitív.

---

 Jellemzők

- Gyökérszintű invertálható architektúra  
  Az **RSF** nem egy meglévő modell köré épített wrapper: a modell magja maga a csatolási stack. Ha eltávolítod a csatolást, nem marad mögötte **CNN**/**RNN**/Transformer.

- Formális verifikáció  
    A repo nagy mennyiségű bizonyítást tartalmaz, amelyek garantálják:
    - rétegenkénti előremenő/inverz invertálhatóságot,
    - alak-invariánsokat az előre/hátra (forward/backward) menetek között,
    - indexbiztonságot és határhelyességet,
    - regiszter-életciklus biztonságot (nincs use-after-free, nincs double free),
    - rendszerszintű invariánsokat több lépéses nyomvonalakra.

- **GPU**-első (**GPU**-first) implementáció  
  Az **RSF** Futhark kerneleket használ (rsfforward, rsfbackward, trainingstep) **GPU**-kódra fordítva, Zig kötésekkel, amelyek tenzorokat, kontextusokat és futtatást kezelnek. A tervezés **NVIDIA**-stílusú hardvert céloz **CUDA**/OpenCL backende­kkel.

- Szigorú numerikus biztonság  
  A skálaértékek egy konfigurálható tartományra vannak klippelve (alapértelmezés [-5, 5]), és az összehasonlítási toleranciák, a tenzoralakok és az indexaritmetika statikusan (bizonyításokban) és dinamikusan (Zigben) is validálva vannak.

- Batch és szekvencia támogatás  
  A mag támogatja a [batch, 2dim] tenzorokat, valamint batch-elt szekvencia elrendezéseket a batchforward és kapcsolódó segédek révén.

---

 Projektstruktúra

rfsaccel/
    rsfaccelfutharkkernels.fut    Futhark **GPU** kernelek (forward, backward, scatter, train step)
    rfsaccelmain.fut              Futhark belépési pontok
    rfsaccelfutharkbindings.zig   Zig kötések a Futhark C **API**-hoz
    rfsaccelfuthark.pkg           Futhark csomagmanifest

rfs/  (vagy rsfcore.zig / rsf.zig)
    RSFLayerConfig, RSFConfig     Konfigurációs struktúrák
    LayerCore                     Súlyok, biasok, gradiensek rétegenként
    Tenzor segédprogramok         clone, allclose, alakvalidálás
    Modell életciklusa            init, deinit, save, load
    Számítási útvonalak           forward, inverse, backward (**CPU** + **GPU**)

proofs/  (Twelf / Beluga)
    rsf-full-invertibility
    completeshapepreservationtheorem
    completeindexsafetytheorem
    completeregistrysafetytheorem
    full-system-safety

Ellenőrizd a repository elrendezését, és igazítsd ezeket az útvonalakat a tényleges checkoutodhoz.

---

 Buildelés

 Előfeltételek

- Zig 0.11 vagy újabb
- Futhark engedélyezett OpenCL vagy **CUDA** backenddel
- Egy C toolchain (a Futhark által generált C fordításához és a Ziggel való linkeléshez)
- Egy **NVIDIA** **GPU** (vagy bármilyen OpenCL-képes **GPU** teszteléshez)

 Lépések

 1. Futhark kernelek buildelése

Az rfsaccel/ könyvtárból:

bash futhark opencl rsfaccelfutharkkernels.fut vagy **CUDA**-hoz: futhark cuda rsfaccelfutharkkernels.fut

Ez legenerálja a C kódot és headereket, amelyeket a Zig kötések használnak.

 2. A Zig könyvtár/bináris buildelése

A repo gyökeréből:

bash zig build

A build.zig script lefordítja a Zig forrásokat, behúzza a Futhark által generált C-t, és linkel a megfelelő OpenCL/**CUDA** könyvtárak ellen.

 3. Tesztek futtatása

bash zig build test

Ez lefuttatja az előremenő/inverz ekvivalenciát, a save/load körbejárásokat és különböző tenzor invariánsokat.

---

 Használat

 Modell inicializálása

zig const rsf = @import(*rfs/rsf.zig*);

var gpa = std.heap.GeneralPurposeAllocator(.{}){}; const allocator = gpa.allocator();

const cfg: rsf.RSFConfig = .{
    .clipmin    = -5.0,
    .clipmax    =  5.0,
    .gradmean   = true,
    .maxdim     = **1024**,
    .maxlayers  = 32,
};

const dim: usize = **256**; const num_layers: usize = 8;

try rsf.validateModelConfigValues(dim, num_layers, cfg); var model = try rsf.initCore(allocator, dim, num_layers, cfg); defer model.deinit(allocator);

 Előremenő menet (forward pass)

zig var input  = try Tensor.init(allocator, .{ batch_size, 2  dim }); var output = try Tensor.init(allocator, .{ batch_size, 2  dim }); defer input.deinit(allocator); defer output.deinit(allocator);

try model.forward(&input, &output);

 Inverz menet (inverse pass)

Az **RSF** pontos invertálhatóságot garantál (lebegőpontos pontosságig):

zig var recon = try Tensor.init(allocator, .{ batch_size, 2  dim }); defer recon.deinit(allocator);

try model.inverse(&output, &recon); // recon ≈ input

 Tanítási lépés (training step)

zig
try model.trainingStep(
    &inputs,
    &targets,
    learning_rate,
    momentum,
);

A motorháztető alatt ez a Futhark trainingstep belépési pontot hívja, amely elvégzi:

1. batchforward
2. batchcomputeloss (**MSE**)
3. batchgradients
## SGD + momentum frissítés sweight, tweight, sbias, tbias paramétereken

 Mentés / Betöltés

zig try model.save(*model.rsf*);

var loaded = try rsf.load(allocator, *model.rsf*, cfg); defer loaded.deinit(allocator);

A bináris formátum verziózott headert és **CRC** ellenőrzéseket tartalmaz.

---

 Formális garanciák

| Tétel | Garanciák |
|---|---|
| rsf-full-invertibility | Rétegenként az előremenő és az inverz kölcsönös inverzei egymásnak |
| rsf-multi-invertibility | N réteg stackje end-to-end invertálható |
| completeshapepreservationtheorem | Az előremenő és a backward globálisan megőrzi a tenzor alakokat |
| completeindexsafetytheorem | Minden súly/bias indexszámítás határon belül van |
| completeregistrysafetytheorem | Nincs use-after-free; a végső takarítás garantált |
| full-system-safety | Rendszerszintű nyomvonalak end-to-end megőrzik az összes invariánst |

---

 Architektúra: miért új gyökérszintű család az **RSF**

Az **RSF** ugyanazt a kritériumot teljesíti, amelyet a Transzformer gyökérszintű architektúraként való besorolásához használtak **2017**-ben: a teljes modell egy új elsődleges számítási primitív köré szerveződik, nem pedig egy korábbi család köré, amelyre csak egy wrapper kerül.

| Tulajdonság | Perceptron | CNN | RNN/LSTM | Transzformer | RSF |
|---|---|---|---|---|---|
| Elsődleges primitív | f(Wx+b) | lokális konvolúció | kapuzott rekurzió | attention | invertálható csatolás |
| Tervezésből fakadóan invertálható | ✗ | ✗ | ✗ | ✗ | ✓ |
| Formális bizonyítási réteg | ✗ | ✗ | ✗ | ✗ | ✓ |
| Attention szükséges | — | — | — | ✓ | ✗ |
| Explicit pozicionális kódolás | — | — | — | ✓ | ✗ |
| GPU-natív tervezés | — | ✓ | részleges | ✓ | ✓ |

---

 Mikor érdemes **RSF**-et használni

Az **RSF** jó választás, ha:

- Pontos invertálhatóság értékes (flow-alapú generatív modellek, reverzibilis enkóderek, veszteségmentes reprezentáció-audit).
- Memóriahatékonyság számít: reverzibilis rétegek O(1) aktivációmemóriát tesznek lehetővé backprop során.
- Formális biztonsági garanciák (alak, indexelés, életciklus) szükségesek.
- Olyan architektúrákat akarsz felfedezni, amelyek a négy klasszikus családon túlmutatnak, miközben szabványos **NVIDIA** **GPU** infrastruktúrán maradsz.

---

 Állapot és korlátok

Ez a repository az alábbiakra fókuszál:

- az **RSF** magréteg-stackre és a kapcsolódó formális bizonyításokra,
- egy **GPU**-barát Futhark/Zig futtatási útvonalra,
- kernel-szintű tanítási primitívekre (**MSE** loss, momentum **SGD**).

Szándékosan nem tartalmaz feladat-specifikus fejeket, magas szintű training loopokat, vagy többcsomópontos (multi-node) elosztott tanítást. Ezeket az **RSF** mag fölé várható felépíteni.

---

 Licenc

Copyright (c) **2026** Kollár Sándor (egyéni vállalkozó, adószám: **49375309**-1-23) Minden jog fenntartva. / Minden jog fenntartva.

Ez a szoftver és forráskódja Kollár Sándor kizárólagos szellemi tulajdona. Bármilyen felhasználás — ideértve a másolást, terjesztést, módosítást, visszafejtést, valamint magáncélú vagy kereskedelmi felhasználást — kizárólag a szerző előzetes, írásos engedélyével lehetséges. Engedély nélküli felhasználás szerzői jogi jogsértésnek minősül.

Ez a szoftver és a forráskódja Kollár Sándor (egyéni vállalkozó, adószám: **49375309**-1-23) kizárólagos szellemi tulajdona. Bármilyen felhasználás — ideértve a másolást, terjesztést, módosítást, visszafejtést, magáncélú vagy kereskedelmi felhasználást — szigorúan tilos a szerző előzetes, írásos engedélye nélkül. Az engedély nélküli felhasználás szerzői jogi jogsértésnek minősül.
