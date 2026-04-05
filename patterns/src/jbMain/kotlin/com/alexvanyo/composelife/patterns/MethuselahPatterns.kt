/*
 * Copyright 2022 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.patterns

import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.toCellState
import com.livefront.sealedenum.GenSealedEnum

sealed class MethuselahPattern(
    patternName: String,
    seedCellState: CellState,
    cellStates: Map<Int, CellState>,
    /**
     * The number of generations for which the pattern is exhibiting interesting behavior.
     */
    val lifespan: Int,
) : GameOfLifeTestPattern(
    patternName = patternName,
    seedCellState = seedCellState,
    cellStates = cellStates,
) {

    @GenSealedEnum(generateEnum = true)
    companion object
}

@Suppress("LargeClass")
data object Pattern52448M : MethuselahPattern(
    patternName = "52448M",
    seedCellState =
    $$"""
        #N 52448m.rle
        #C https://conwaylife.com/wiki/52513M
        #C https://www.conwaylife.com/patterns/52448m.rle
        x = 11, y = 35, rule = B3/S23
        4b2o$2b2o2$bo$bo$bo6$3bobo2$4bo$4bo$4bo9$7bo$7b2o$6bo3$o8b2o$b2o6bo2$b
        o$b2o$o!
    """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
    cellStates = mapOf(
        52448 to $$"""
            #R -13055 -13000
            x = 26139, y = 26077, rule = B3/S23
            3o$o$bo81$25986b3o$25988bo$25987bo14$25990b2o$25989bobo$25991bo208$
            451b2o$451bobo$451bo60$25809b3o$25811bo$25810bo32$25771b3o$25773bo$
            25772bo21$25773b2o$25774b2o$25773bo33$25691b2o$25692b2o$25691bo64$
            25676bo$25676b2o$25675bobo53$25569bo$25569b2o$25568bobo138$865bo$864b
            2o$864bobo285$960bo$959b2o$959bobo52$24958b2o$24959b2o$24958bo172$
            24636b2o$24635bobo$24637bo18$24568b2o$24567bobo$24569bo68$1311b2o$
            1311bobo$1311bo65$1450bo$1449b2o$1449bobo235$1679bo$1678b2o$1678bobo
            198$1801b2o$1800b2o$1802bo166$23832b2o$23833b2o$23832bo25$23811b2o$
            23810bobo$23812bo33$23738b2o$23737bobo$23739bo62$2285b2o$2285bobo$
            2285bo291$2389bo$2388b2o$2388bobo18$23243bo$23243b2o$23242bobo50$
            23212b2o$23213b2o$23212bo179$22977b2o$22976bobo$22978bo72$2614bo$2613b
            2o$2613bobo15$2676bo$2675b2o$2675bobo13$2792b2o$2791b2o$2793bo467$
            3256bo$3255b2o$3255bobo51$3182b2o$3181b2o$3183bo39$22159b2o$22158bobo$
            22160bo457$3743b2o$3743bobo$3743bo205$4008b2o$4007b2o$4009bo30$21435b
            2o$21434bobo$21436bo34$21467bo$21467b2o$21466bobo69$4152b3o$4152bo$
            4153bo84$21089b3o$21091bo$21090bo170$21105b2o$21104bobo$21106bo374$
            4958b2o$4958bobo$4958bo18$20668b3o$20670bo$20669bo3$4968bo$4967b2o$
            4967bobo17$4945bo$4944b2o$4944bobo96$20423b2o$20422bobo$20424bo86$
            20451bo$20451b2o$20450bobo132$5434b2o$5434bobo$5434bo2$20523b3o$20525b
            o$20524bo6088$14289b2o$14288bobo$14290bo1124$12514bo$12513b2o$12513bob
            o146$12408b2o$12408bobo$12408bo45$12805bo$12804bobo$12805bo14$12792b2o
            $12792b2o5$12838b2ob2o$12774b2o62b2ob2o$12774b2o4$12791bo$12790bobo32b
            3o$12790bobo$12791bo$12763b2o$12763bobo20b2o7b2o$12764b2o19bo2bo5bo2bo
            $12786b2o7b2o$12804b2o$12791bo12b2o$12790bobo42bo$12790bobo42bo$12791b
            o43bo$12692b2o123bo$12683bo8b2o123bo$12683bo124b2o7bo$12683bo124b2o$
            12802b3o8b3o3b3o2$12806bo10bo$12798bo7bo10bo11b3o$12798bo7bo10bo$
            12798bo2$12794b3o3b3o17bo$12689bo72b2o55bobo$12689bo72b2o5bo28bo19bo2b
            o$12689bo78bobo27bo20b2o$12769bo28bo$12685b3o3b3o$12764b2o$12764b2o4b
            2o2b2o100b2o3b2o$12770b2o2b2o66b2o32b2o2bo2bo$12807b2o32bo2bo36b2o$
            12807b2o33bobo$12843bo$12708b2o109b3o15b2o58b3o$12708bobo44bo81b2o23bo
            $12709b2o43bobo60bo43bobo$12754bo2bo47bo11bo22b2o19bo2bo$12755b2o32b2o
            14bo11bo22b2o20b2o$12788bo2bo13bo$12789b2o28b3o61b2o$12883b2o$12793b2o
            $12789b2o2b2o$12789b2o42bo$12832bobo6bo8bo$12824b2o6bobo6bo7bobo28b2o$
            12661b2o67b2o91bo2bo6bo7bo7bo2bo27b2o$12661b2o66bo2bo91b2o24b2obo$
            12730b2o120bobo$12722bo129bo2bo$12715bo6bo79bo50b2o$12715bo6bo71b2o5bo
            bo$12715bo77bo2bo5bo34bo30b2o$12703bo46b3o41b2o40bobo29b2o$12702b2o74b
            2o56bo2bo$12702b2o44bo5bo23b2o57b2o17bo$12673b2o27bo45bo5bo101bo$
            12673bobo72bo5bo101bo$12643b2o29bo3b2o208b2o$12642bo2bo32b2o57b2o11b3o
            70bo64b2o$12643b2o88bo3b2o84bo$12732bobo43b2o43bo$12653bo40bo36bo2bo
            43b2o$12652bobo38bobo36b2o170bo27b2o$12652bobo37bo2bo107bo100bo27b2o$
            12653bo39b2o108bo100bo$12673b2o128bo$12648b2o7b2o14b2o176b2o71b2o$
            12647bo2bo5bo2bo132bo6b3o3b3o37bo5b2o71b2o$12648b2o7b2o133bo51bobo$
            12792bo10bo35b2o3bobo$12653bo149bo34bo2bo3bo11b2o$12652bobo60b2o86bo
            35b2o16b2o37b2o45b2o$12652bobo3bo56bobo4b2o171bo2bo43bobo$12653bo3bobo
            5b2o49bo5b2o55b2o10b2o103b2o44b2o$12658b2o5b2o52bo59b2o10bobo51b2o$
            12719bo72bo52b2o$12719bo37b2o$12757b2o162b2o$12661bo35b2o16b3o3b3o22b
            2o173b2o$12660bobo9b2o23b2o46bo2bo26b2o129b2o$12660bobo9b2o72bobo26b2o
            90b2o37b2o$12661bo85bo119b2o14b2o15bo$12625b2o51b2o113b2o88b2o14bobo$
            12624bo2bo50b2o113b2o104bobo$12625b2o209b2o62bo$12652b3o180bo2bo$
            12736b2o98b2o57b2o7b2o$12665bo16b3o35bo8b2o5b2o17b2o137bo2bo5bo2bo$
            12665bo53bobo7b2o23bo2bo137b2o7b2o$12665bo52bo2bo33bobo$12719b2o35bo
            143bo$12661b3o3b3o40bo188bobo$12709bobo16b2o20b2o147bobo$12665bo43bo2b
            o14bo2bo19b2o81b2o22b2o16b2o23bo$12665bo44b2o16b2o103b2o22b2o16b2o$
            12637bo7b2o18bo$12637bo7b2o150b3o72b2o$12637bo234bobo$12662b2o209bo$
            12661bobo$12661b2o2$12703b2o139b2o8b3o24bo$12703b2o139b2o35bo$12839bo
            41bo$12661b2o175bobo$12660bo2bo174bobo$12661b2o23bo152bo35b2o$12686bo
            88b3o4b2o91b2o$12686bo95b2o$12718b2o45bo78b2o$12682b3o3b3o26bo2bo43bob
            o77b2o$12652b2o63bo2bo12bo30bobo$12652b2o32bo31b2o13bo31bo$12686bo46bo
            10b3o$12663b2o21bo87b2o40b3o$12663b2o47b2o60b2o$12711bo2bo38bo$12712b
            2o39bo$12753bo$12889b3o$12686bo17b2o108b2o$12685bobo15bo2bo94b2o11b2o
            17bo$12626b2o57bobo16bobo94b2o29bobo$12626b2o58bo18bo4bo121bobo66bo$
            12710bo23b2o18b2o6b2o65bo3bo66bobo$12681b2o7b2o18bo23bobo17b2o6b2o55b
            2o7bobo69bobo$12627b2o51bo2bo5bo2bo42b2o40bo40bo2bo6bobo6b2o62bo$
            12627b2o52b2o7b2o14b3o3b3o61bobo5b2o33b2o8bo6bo2bo9b3o70b2o$12670b2o
            105bo6b2o51b2o50b2o31b2o$12670b2o14bo23bo142bo15bo19b2o$12659bo25bobo
            22bo100bo21bo12b2o5bo15bo$12658bobo24bobo22bo99bobo19bobo11b2o5bo15bo$
            12658bobo25bo72b2o50b2o19bobo56bo17b3o$12659bo99b2o72bo15b3o13b3o3b3o
            16bobo$12890bobo20bo$12671b2o196bo21bo21bo$12671b2o95b2o99bo43bo$
            12759b2o6bobo3b2o94bo17b3o$12759b2o7bo3bobo$12773bo111bo5bo$12885bo5bo
            6bo$12620b2o206b2o55bo5bo6bo$12620b2o206bobo67bo$12829bo57b3o$12662b2o
            172b3o37bo$12662b2o88b2o39b2o81bo39b3o$12752b2o7b2o30b2o81bo$12761b2o
            26b2o129bo$12707b3o79b2o6b2o87bo20b2o11bo$12797b2o87bo19bo2bo10bo$
            12660bo43bo181bo20b2o$12660bo43bo$12639bo20bo43bo$12607bo31bo44bo92bo
            124bo$12607bo31bo43bobo20b3o56b3o9bo43b2o5b2o63b3o5bobo$12607bo20b2o
            53bobo91bo43b2o5b2o12b2o8bo48bobo$12627bobo5b3o3b3o40bo56bo99bo2bo7bo
            49bo$12603b3o22bo111bobo99b2o8bo$12639bo39b2o7b2o32b2o16bobo14b3o146bo
            $12639bo38bo2bo5bo2bo9b2o19bo2bo16bo43bo120bo$12639bo39b2o7b2o10b2o20b
            2o61bo120bo$12611bo173bo$12611bo31b2o39bo58b2o135bo27b3o$12611bo26bo4b
            2o38bobo34bo21bo2bo3b3o57bo70bo$12638bo44bobo34bo22b2o63bobo69bo25bo$
            12638bo45bo35bo86bobo73b2o21bo$12653bo154bo33b2o39b2o21bo$12652bobo
            116b2o69b2o$12653bo63bo53b2o$12716bobo69b2o$12716bobo69b2o$12638bo78bo
            181bo$12638bo102b2o105b2o49bo$12638bo72b2o28b2o104bo2bo48bo$12711b2o
            70bo63bobo$12607b2o25b3o3b3o140bo64bo$12607b2o174bo$12638bo$12638bo10b
            3o121b3o$12611b2o17b2o6bo186b2o73b2o$12603b3o4bo2bo15bobo192bo2bo72b2o
            $12611b2o17bo194b2o$12601bo5bo16b2o38b3o33bo$12557b2o17b2o23bo5bo15bob
            o74bo166bo32b2o6b2o$12557b2o16bo2bo22bo5bo15b2o75bo166bo32b2o6b2o$
            12576b2o52b2o235bo$12603b3o23bo2bo47b2o232b2o$12630b2o47bo2bo186b3o42b
            2o$12679bo2bo262b2o$12680b2o26bo20bo36b2o15b2o82bo77b2o$12646bo60bobo
            19bo32b2o2b2o15b2o82bo$12571bo74bo61bo20bo32b2o103bo$12546b2o23bo74bo
            67bo$12546bobo12b2o8bo45b2o68b2o25bo10b3o3b3o151bo$12547b2o12b2o54bobo
            67b2o25bo67b2o100bobo40b2o$12567b3o3b3o42b2o109bo44bo7b2o51b2o48bo41b
            2o$12720b2o7bo43bobo25bo33bobo$12555b3o13bo136b2o10b2o7bo43bo2bo24bo
            34bo19b2o$12571bo135bo2bo63b2o25bo53bo2bo76b2o$12553bo5bo11bo136b2o59b
            2o84bo2bo76b2o$12553bo5bo209b2o55b2o28b2o5b2o$12553bo5bo266b2o35b2o$
            12663b2o$12595b2o38b2o26b2o37b2o$12533b2o59bo2bo37b2o2b2o61b2o46b2o$
            12532bo2bo59b2o42b2o108bo2bo34b2o6b2o$12533b2o73b3o114bo24b2o35b2o6b2o
            $12725bo56b3o$12612bo112bo15b2o71b3o$12612bo128b2o19b2o42b2o34b2o$
            12530b3o79bo14bo3b2o114b2o13b2o42b2o10bo22bo2bo48bo$12554b2o70bobo2b2o
            101b2o11b2o69bo23b2o15b2o31bobo$12554b2o52b3o15bobo106bo82bo36b2o2b2o
            31bobo73b2o$12530bo46bo13b2o34bo104bo19b2o36bo22b2o40b2o36bo74b2o$
            12529bobo13b2o30bo13b2o139b2o17bo2bo35bo22b2o15b2o$12529b2o14b2o30bo
            39bo90b2o42bobo35bo12b2o25b2o$12616bobo89b2o19bo23bo49b2o8b2o$12573b3o
            3b3o34bobo109bobo55b3o3b3o18b2o42bo27b2o$12617bo87b2o20bo2bo126bo27b2o
            $12556b2o11b2o6bo127b2o21b2o60bo66bo$12551b2o2bo2bo10b2o6bo212bo$
            12526b2o23b2o3b2o19bo70b3o34b2o103bo102b2o$12526b2o157b2o205bo2bo81bo$
            12639b2o206bo45bobo81bo$12639b2o2b2o87b2o112bobo45bo55b2o25bo8b2o$
            12563b2o78b2o87b2o112bobo100bo2bo17b2o14b2o$12562bo2bo171b2o108bo102b
            2o18b2o$12563b2o146b2o3b2o18bo2bo$12550b2o159b2o3b2o19b2o14bo133b2o17b
            o$12550b2o201bo133b2o16bobo$12614bo138bo89bo61bobo$12613bobo118b2o106b
            obo21b3o37bo41bo30b2o$12593b2o18bobo117bo15b3o3b3o84bobo33b2o67bobo29b
            2o$12544bo47bo2bo18bo37b2o17b2o63bo32b2o62bo9bo34b2o68bo$12520b2o22bo
            48b2o57b2o17b2o61b2o17bo14bo2bo60bobo$12520bobo21bo12bo50b2o143bo15b2o
            27b2o32bobo88bo15b2o$12521b2o33bobo42bo6b2o143bo44b2o33bo88bobo14b2o8b
            2o$12552b3o2bo41bo2bo70b2o102b3o143bo25b2o$12539bo59bo2bo70b2o16bo$
            12539bo39bo20bo49bo39bobo250b2o$12539bo38bobo68bobo38bobo192b2o56b2o$
            12578b2o69bobo39bo60b2o131b2o44bo$12535b3o3b3o7b2o97bo101b2o73b2o101bo
            bo$12550bobo274b2o23b2o76bobo$12539bo11bo17bo4b2o275bo2bo76bo$12539bo
            28bobo2bo2bo50b2o21b2o200b2o13bo$12539bo28bobo3b2o50bo2bo20b2o215bo28b
            o$12569bo56bobo238bo27bobo53b2o$12536bo54bo35bo186b2o4bo39b2o33b2o54b
            2o$12536bo53bobo147bo35bo9bo27b2o3bobo37bo2bo$12536bo54bo45bo101bobo
            33bobo7bobo31bobo37bo2bo$12544b2o63b2o25bobo100b2o35b2o7b2o33bo39b2o
            88b2o13b3o$12544b2o25b2o36b2o8b2o15bo2bo213b2o89b2o4b2o$12571b2o46b2o
            16b2o92b2o48bo70bo2bo87bo2bo16bo5bo$12583bo123b2o22b2o47bobo69bobo89b
            2o17bo5bo$12583bo123b2o71bobo70bo109bo5bo$12583bo197bo128b2o$12569b2o
            124b2o213b2o53b3o$12569b2o124b2o189b3o2$12687b2o27bo255b2o$12659b2o26b
            2o27bo46b2o44b3o116b2o42b2o19b3o$12659b2o55bo46b2o79b3o52b2o27b2o$
            12877b2o20b2o$12609b2o74bo52b2o137bobo101bo$12609b2o74bo51bo2bo43b2o
            92bo93b2o6bobo$12638b2o24b2o19bo52b2o44b2o147b2o37b2o6bobo$12638b2o24b
            2o27b2o104b2o132b2o46bo$12623bo69b2o104b2o$12553b2o3b2o4b2o21b3o33bo
            136b2o151bo64b2o$12553b2o3b2o4b2o7b2o48bo78b3o55b2o75b3o72bobo63b2o$
            12573bobo293b2o41bobo$12574bo15b2o54b2o95b2o113b2o9b2o15b2o25bo$12590b
            2o23bo30b2o95b2o70b2o40bo2bo24bo2bo5bo$12615bo39b2o44b2o25b3o84b2o41bo
            bo25b2o5bobo12b2o7b2o58b3o9bo$12615bo6b3o30b2o44b2o139b2o15bo32bo2bo
            11bo2bo5bo2bo30bo37bobo$12650b2o190b2o38bo10b2o13b2o7b2o31bo37bobo$
            12650b2o85b2o24bo42b2o57b3o13bobo66bo38bo$12613b3o121b2o23bobo41b2o72b
            o2bo29bo$12621bo141bo99bo5bo11b2o29bobo55bo13b2o7b2o48b3o$12620bobo32b
            3o30b2o51bo121bo5bo42bobo55bo12bo2bo5bo2bo$12620bobo65b2o50bobo10b2o
            12bo95bo5bo43bo14b2o40bo13b2o7b2o$12621bo118bo2bo9b2o11bobo158bo2bo$
            12635b2o11b2o91b2o23bobo89b2o5b3o59bo2bo58bo$12634bo2bo10b2o111bo5bo
            82b3o4bo2bo67b2o44b2o12bobo$12551b3o23b2o22b2o32b2o124bo96b2o59b2o31b
            2o20b2o12bobo$12577b2o22b2o158bo156bo2bo30b2o35bo$12571b2o98bo246bobo$
            12571bobo97bo29b3o215bo$12572b2o56b3o38bo86b2o250b2o$12619b2o22b2o43bo
            10bo12bo32bo11bo2bo164b2o40bo19b2o21b2o$12619b2o22b2o38b2o2bobo9bo12bo
            32bo12b2o9bo89b2o6b3o55b2o39bobo18b2o$12635b2o46b2o2bobo9bo12bo5bo26bo
            22bobo88b2o25b2o77bobo53b2o$12635b2o10bo30b2o8bo28bobo41b3o4bobo21b2o
            43b2o47b2o78bo54b2o$12646bobo29b2o21b3o4b3o6b2o50bo21bo2bo42b2o36b2o
            154b2o$12614b2o30bobo17b2o124b2o81bobo57b2o69bo24b2o7bo$12614b2o31bo
            18b2o208b2o50b3o4b2o68bobo31bobo$12745bo5bo10b2o240bo2bo31bobo$12611bo
            58b2o18bo54bo5bo9bo2bo240b2o33bo$12611bo58b2o6b2o9bobo53bo5bo10b2o80bo
            $12611bo65bo2bo8bobo123bo27bobo112bo$12678b2o10bo56b3o64bobo27bo34b2o
            34bo42bo88b2o$12814b2o63b2o5b2o27bo29b2o11bo87bobo$12687b2o7b2o89b2o
            97b2o9b2o16bo29b2o99b2o$12647b2o37bo2bo5bo2bo88b2o56b2o50b2o55b3o3b3o
            14bo$12646bo2bo37b2o7b2o122b3o22b2o130bo$12646bobo170b3o136bo18bo$
            12647bo44bo265bo14bo14bo21b2o$12664bo26bobo147b2o111bo3bo13bobo12bobo
            20b2o$12663bobo25bobo28b2o14b2o100bo2bo110bo16bo2bo12bobo9b2o$12643bo
            19bobo11b2o13bo28bo2bo13b2o101b2o37b2o29b3o40bo17b2o14bo9bo2bo$12642bo
            bo19bo12b2o42bo2bo154bo2bo116b2o$12643bo66b3o9b2o156b2o174b2o$12672b2o
            382b2o$12671bobo153bo$12664bo7bo24b3o127bo$12663bobo117b2o42bo101b3o$
            12663bo2bo116b2o101bo62bo$12641b2o21b2o74b2o3b2o96bo8b3o30bobo60bobo$
            12640bo2bo86bo11bo2b2o95bobo40bobo60bobo7b3o42b3o7b2o14bo$12641b2o87bo
            8bo103b2o5bo5bo29bo62bo62bo2bo12bobo21b2o$12730bo9b2o108bo5bo85b3o11bo
            35bo20b2o6b2o5bobo21b2o$12850bo5bo65bo33bo22bo12bo28b2o6bo$12763b2o
            156bobo16bo5bo9bo5bo16bo12bo$12762bo2bo86b3o65bo2bo16bo5bo14bobo15bo
            57b2o$12763b2o93b3o60b2o17bo5bo13bo2bo24b3o3b3o39bobo$12676bo127b2o
            155b2o12b3o3b3o53bo$12629b2o45bo127bobo125b2o8b3o47bo$12629b2o45bo96b
            3o29bobo118b2o4b2o45bo12bo$12806bo118bo2bo41b2o7bo12bo$12657bo122bo50b
            o93bo2bo33b2o6b2o7bo$12656bobo83b2o35bobo41b2o6bo23b3o68b2o34b2o$
            12629b2o25bo2bo71b2o8bo2bo6bo27bobo41b2o6bo227bo$12629b2o26b2o72b2o9b
            2o6bobo27bo11b2o8b2o255bo$12715bo35b2o38bo2bo7b2o161b2o92bo$12714bobo
            75b2o104bo66b2o149bo$12714bobo180bobo33b2o88b2o30b3o3b3o51bobo$12715bo
            17b2o13b2o146bo2bo33b2o87bo2bo89bobo$12733b2o12bo2bo97b2o47b2o77b2o45b
            2o34bo56bo$12748b2o98b2o126b2o81bo$12724b2o156b2o36b2o137bo$12708b2o
            13bo2bo3b2o12bo38bo98b2o35bo2bo$12660bo46bo2bo13b2o3bo2bo10bobo36bobo
            46b3o86b2o$12659bobo45bobo19bobo11bobo35bo2bo$12659bobo46bo21bo13bo37b
            2o187bo$12660bo38bo162b2o106bobo77b2ob2o$12651bo46bobo160bo2bo10b2o93b
            2o78b2ob2o$12650bobo45b2o124b3o18b2o14bobo11b2o16b3o$12650bobo4b3o112b
            o61bo10b2o15bo$12651bo120bo15b3o26b2o14bobo48b3o10bo65b2o134b3o$12730b
            o41bo44b2o15bo24bo37bo65b2o25bo$12716b2o11bobo127bo22bo5bo8bo39b2o50bo
            bo22b2o$12715bo2bo10bobo36b3o3b3o35b2o45bo22bo5bo15b3o29bo2bo49b2o22bo
            bo28b2o$12705b2o9bobo11bo81b2o68bo5bo4b3o41bobo73b2o29b2o5b2o$12705b2o
            10bo184bo5bo29bo101b2o9bobo60b2o$12758b2o67b2o19b3o33b3o15bo5bo130bo2b
            o9bo60bo2bo$12758b2o67b2o34b2o37bo5bo131b2o72bobo$12694b2o19b2o146b2o
            250bo7bo$12694b2o2b2o14bo2bo186b3o85b2o63b2o63bobo$12698b2o15b2o275b2o
            8b2o53b2o2b2o59b2o$12912bo89bobo56b2o$12772b2o28b2o108bo90b2o14b2o$
            12772b2o27bo2bo59b2o22bo13b2o8bo106b2o$12802b2o60b2o21bobo11bo2bo178bo
            29b3o$12692b3o31b2o159bo2bo11b2o74bo103bobo$12725bo2bo159b2obo86bo103b
            obo$12703b2o21b2o162bobo85bo104bo$12703bobo92b2o90bo2bo$12685bo18bo93b
            2o69b2o20b2o194b2o41bo$12685bo51b3o52b3o73bo2bo214bobo40bobo50b3o$
            12685bo174b2o7b2o107bo108bo41bobo$12790bo5bo62bo2bo115bo151bo49bo5bo$
            12790bo5bo63b2o17b2o97bo146bo54bo5bo$12718bo17b2o52bo5bo82b2o29b3o33bo
            177bobo53bo5bo$12717bobo16b2o192b2o13bobo176bobo70b3o$12700b2o14bo2bo
            72b3o113bo5bo15b2o13bobo10bo166bo56b3o$12699bo2bo14b2o174bo6b2o6bo5bo
            31bo10bobo214b2o$12700b2o191bo5bo2bo5bo5bo15b2o25bobo51bo156b3o2bo2bo$
            12893bo6b2o21b2o5b2o26bo52bo57b2o103b2o$12696bo213b3o10b2o86bo57b2o$
            12695bobo163bo65bo5bo19b2o7b2o$12695bobo162bobo64bo5bo18bo2bo5bo2bo42b
            3o9b2o133b3o$12696bo163b2o20b2o43bo5bo19b2o7b2o55b2o108b2o$12882b2o
            154b2o89b2o21bo5bo$12711b3o6bo208b3o26bo41b2o36b2o76b2o34bo5bo$12686bo
            33bo135b2o85bo13bobo40b2o20bo93b2o34bo5bo$12685bobo21bo5bo4bo57b2o75bo
            2bo83bobo12bobo61bobo190b2o$12686bo22bo5bo12b3o47bobo75b2o29b2o53bobo
            13bo62bobo53b2o12bo62b3o41b2o14b2o$12709bo5bo6b3o54b2o105bo2bo53bo32b
            2o13bo30bo53bo2bo10bobo18b2o85b2o$12887b2o87b2o12bobo84b2o11bobo18b2o
            3b2o$12711b3o146b2o5b2o121b2o99bo24bobo$12860bobo4b2o204bo43bobo10bo$
            12861bo76b2o40b2o50b2o38bobo43bo10bobo58bo$12937bo2bo39b2o11b2o36bo2bo
            37bobo54bobo7b2o49bo$12741b2o195b2o52bo2bo35bobo39bo56bo8b2o23b2o24bo$
            12729bo11b2o250b2o8b2o27bo130bo2bo$12728bobo212bo25b2o32b2o159b2o$
            12720b2o6b2o3b2o207bobo24b2o233b2o$12719bo2bo10bobo175b3o28bobo54b3o
            13b2o187bobo$12720b2o12b2o207bo71b2o188bo$12930b2o16b2o47bo5bo24bo125b
            o65bo5b2o$12738b2o189bo2bo15b2o47bo5bo24bo124bobo41bo21bobo4b2o$12737b
            o2bo188bo2bo64bo5bo24bo125bo26b2o14bo21b2o$12738b2o190b2o118b2o128bo2b
            o13bo$12999b3o47bo2bo128bobo$12697b2o36b2o313b2o130bo30b2o$12697b2o6b
            3o27b2o475bo2bo$13006b2o76bo39b3o86b2o$13006b2o76bo$13049b2o33bo37bo5b
            o$12932b2o115b2o19b2o50bo5bo$12931bo2bo21bo113b2o14b3o33bo5bo101b3o$
            12932b2o9b2o11bo139b2o$12943b2o11bo139b2o26b3o101bo5bo$13042b2o184bo5b
            o$12952b3o3b3o81b2o184bo5bo$12971b2o183b2o9b2o53b2o$12956bo14b2o85bo
            96bo2bo8b2o52bo2bo$12956bo5b2o93bobo96b2o49b2o13b2o$12956bo4bo2bo92bob
            o82bo52b2o10b2o$12962b2o16b2o76bo82bobo34bo16b2o20b2o38b2o$12973bo6b2o
            159bobo9bo24bo37bobo38b2o$12973bo17b2o149bo9bobo23bo38bo30b2o$12973bo
            17b2o159bobo93b2o4b2o10b2o$13153bo86b3o10bobo9bo2bo9b2o$13169b2o83bo
            11b2o4bo5b2o$13049b2o15bo102b2o38b2o60bobo$13048bo2bo13bobo9b2o110bo
            19b2o59bo2bo$13029bo19bobo14bo9bo2bo108bobo80b2o$13028bobo19bo26b2o
            110bo52bo$13028bobo79bo121b2o7bobo$13029bo79bobo120b2o7bo2bo$13109b2o
            50b2o53bo25b2o$13103b2o56b2o53bo$13102bo2bo110bo$13103b2o$13071bo125b
            2o13b3o3b3o$13070bobo78bo18b2o25b2o25b2o$13070bo2bo77bo18b2o12b2o30bo
            6bo2bo$13071b2o62b2o14bo32b2o30bo7b2o$12990b2o143b2o79bo$12990b2o60b3o
            174bo$13111b2o115bobo$13111b2o115bobo$13132b2o95bo$13132b2o$13026bo97b
            o$13026bo43b3o50bobo$13026bo96b2o$13013b2o53bo5bo$12980b2o31b2o53bo5bo
            85b2o$12980bobo85bo5bo31b3o50bo2bo$12981b2o176bobo3bo$13070b3o87bo3bob
            o$13136b3o25bobo$13165bo$13044b2o$13044b2o58b2o$13104b2o$13115bo29b2o$
            13115bo29b2o$13047b2o66bo$13029bo16bo2bo88b2o$13029bo17b2o89bobo$
            13029bo58bo50bo$13078bo9bo$13031b3o43bobo8bo$13077bo2bo$13078b2o10b3o
            47b2o$13045bo94b2o$13044bobo120b2o$13044b2o86b2o32bobo$13132b2o32b2o$
            13027b2o$13007b2o9bo8b2o6bo107bo$13007b2o9bo15bobo49b2o15bo39bo$13018b
            o15bobo48bo2bo14bo39bo$13035bo36bo13b2o15bo$13006b2o63bobo47b2o$13006b
            2o34b3o26bobo31bo14bo2bo$13072bo32bo15b2o$13105bo43b3o$13117bo$13046b
            2o42b2o24bobo42bo$13046b2o12b2o27bo2bo19bo3bobo42bo$13060b2o28b2o20bo
            4bo43bo$13022b3o87bo$13143bo13b3o3b3o$13143bo$13078bo64bo17bo$13040bo
            37bo82bo$13040bo37bo13b2o67bo$13040bo50bo2bo74b3o$13091bo2bo$13092b2o
            2$13151b2o$13151b2o2$13148b2o$13147bo2bo$13033bo114b2o15b3o$13032bobo$
            13031bo2bo128bo5bo$13032b2o129bo5bo$13163bo5bo2$13165b3o2$13048b2o$
            13048b2o2310$10185bo$10183b2o$10184b2o1916$8128bo$8128bobo$8128b2o48$
            8100bo$8099bo$8099b3o1142$7072bo$6972bo99bobo$6970b2o100b2o$6971b2o
            2158$4589bo$4588bo$4588b3o69$4554bo$4552b2o$4553b2o558$21080bo$21078bo
            bo$21079b2o390$3670bobo$3670b2o$3671bo219$3470bobo$3470b2o$3471bo29$
            3436bo$3435bo$3435b3o114$3769bo$3768bo$3768b3o722$22579bo$22577bobo$
            22578b2o104$2672bobo$2672b2o$2673bo217$2409bo$2409bobo$2409b2o110$
            2379bobo$2379b2o$2380bo28$23061bo$23062bo$23060b3o185$2217bo$2217bobo$
            2217b2o173$23493bo$23491bobo$23492b2o132$2006bobo$2006b2o$2007bo18$
            1996bobo$1996b2o$1997bo41$2172bo$2172bobo$2172b2o221$1857bo$1856bo$
            1856b3o23$24002bo$24003bo$24001b3o180$1537bo$1536bo$1536b3o342$24568bo
            $24569b2o$24568b2o361$25102bobo$25103b2o$25103bo88$25042bo$25040bobo$
            25041b2o6$1044bobo$1044b2o$1045bo231$25503bo$25501bobo$25502b2o38$
            25577bo$25578bo$25576b3o17$635bobo$635b2o$636bo38$666bo$664b2o$665b2o
            11$563bo$561b2o$562b2o$672bo$672bobo$672b2o184$25688bo$25689b2o$25688b
            2o47$496bo$495bo$495b3o40$25868bo$25869b2o$25868b2o12$25773bo$25774b2o
            $25773b2o369$26070bobo$26071b2o$26071bo66bo$26136bobo$26137b2o!
        """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
    ),
    lifespan = 52448,
)

data object BlomPattern : MethuselahPattern(
    patternName = "Blom",
    seedCellState =
    $$"""
        #N Blom
        #O Dean Hickerson
        #C A methuselah with lifespan 23314 found in July 2002.
        #C www.conwaylife.com/wiki/index.php?title=Blom
        x = 12, y = 5, rule = B3/S23
        o10bo$b4o6bo$2b2o7bo$10bob$8bobo!
    """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
    cellStates = mapOf(
        23314 to $$"""
            #R -5766 -5805
            x = 11432, y = 11593, rule = B3/S23
            3b2o$2b2o$4bo68$3o$o$bo70$11348b2o$11347bobo$11349bo12$56bo$55b2o$55bo
            bo24$11403b3o$11405bo$11404bo37$11429b2o$11430b2o$11429bo74$438bo$437b
            2o$437bobo12$393b2o$393bobo$393bo15$164b2o$163b2o$165bo11$215b3o$215bo
            $216bo130$11204b2o$11205b2o$11204bo1006$10219bo$10219b2o$10218bobo160$
            9826b2o$9827b2o$9826bo1852$8372bo$8372b2o$8371bobo822$4000b3o$4000bo$
            4001bo198$4066b2o$4066bobo$4066bo189$4378b2o$4377b2o$4379bo60$4432b2o$
            4431b2o$4433bo172$4605bo$4604b2o$4604bobo87$4635b3o$4635bo$4636bo113$
            4900b2o$4899b2o$4901bo573$5790b2o73b2o$5790b2o73b2o4$5774bo$5773bobo$
            5773bobo8bo$5774bo8bobo$5783bobo96b2o$5769b2o13bo97b2o$5768bo2bo$5769b
            2o2$5876b2o$5826b2o4b2o42b2o$5826b2o4b2o3$5783bo$5782bobo23bo19b2o$
            5766b2o14bo2bo21bobo18b2o$5765bo2bo14b2obo21b2o57b2o$5766b2o17bobo79b
            2o$5785bo2bo62b2o$5775b2o9b2o63b2o20bo$5775b2o95bobo$5838b2o32b2o$
            5771b3o55b2o7b2o$5829b2o90b3o3$5808b3o2$5770bo87b2o$5769bobo85bo2bo$
            5769bobo86bobo63b2o$5737b2o31bo88bo64b2o$5737b2o135b2o$5765b2o107b2o
            10bo$5764bo2bo75bo34b3o4bobo$5765b2o75bobo40bobo$5842bobo41bo3b2o$
            5743bo26bo12bo20bo38bo16b3o26bobo$5743bo25bobo10bobo19bo83bobo$5743bo
            11b2o3b3o6bobo10bobo19bo33b2o24bo24bo$5726b2o27b2o13bo12bo53bo2bo23bo$
            5726bobo10b3o3b3o52b3o35b2o24bo$5727b2o49b2o7b2o21bo8bo$5777bo2bo5bo2b
            o20bo7bobo21b2o51bo$5742b2o18b2o14b2o7b2o21bo8b2o20bo2bo49bobo$5742b2o
            18b2o78b2o50bobo$5751bo31bo111bo$5750bobo29bobo$5749bo2bo29bobo$5750b
            2o31bo$5808bo24b3o59b2o3b3o3b3o$5808bo85bo2bo$5752b2o41b3o10bo86b2o7bo
            $5752b2o32bo27b2o26b3o19b2o38bo$5786bo27b2o21b2o25b2o17b2o19bo$5786bo
            49bo2bo43b2o44bo$5837b2o90bo$5756b3o29b3o138bo2$5786bo$5778b2o6bo28b2o
            10bo$5778b2o6bo27bo2bo9bo$5792b3o20b2o10bo$5775b2o9bo64b2o$5751b2o21bo
            2bo7bobo63b2o33bo$5751b2o22b2o9b2o97bobo$5744b2o139bobo$5744b2o117b2o
            21bo$5863b2o59b2o$5924b2o$5807b2o$5807b2o$5772bo84b2o47b2o12b2o$5771bo
            bo70b2o10bo2bo46b2o12b2o$5771bobo70b2o11bobo22bo$5772bo85bo22bobo$
            5743b2o124b3o9bo2bo$5743b2o137b2o$5749b2o18b2o85b2o$5749b2o17bo2bo3b2o
            45bo32bo2bo4b2o$5769bobo3bobo11b2o14b2o15bo33b2o5b2o10bo$5666b2o102bo
            5bo12b2o14bobo14bo51bobo10bo$5666b2o78b2o36b2o20bo67bobo9bobo16b3o$
            5746b2o36b2o32b3o3b3o48bo10bobo$5731bo155bo$5674b2o54bobo89bo19b2o9bo$
            5674b2o54bo2bo88bo18bobo8bobo16bo10b2o7b2o$5731b2o65bo23bo19bo9bobo16b
            o9bo2bo5bo2bo$5797bobo53bo17bo10b2o7b2o$5796bo2bo$5655b2o140b2o13b2o4b
            2o47b3o3b3o11bo$5655bobo154b2o4b2o66bobo$5656b2o35bo30b2o20b2o46bo76bo
            14bobo$5693bo30b2o20b2o36bo9bo13bo62bo15bo$5693bo90bo9bo12bobo61bo$
            5784bo22bobo$5689b2o99b3o5bo9bo$5689b2o15bo91bo$5705bobo90bo$5704bo2bo
            137bo$5705b2o87b3o5bo41bobo$5802bo5b2o34bobo$5802bo5b2o10b2o23bo$5820b
            2o$5729b2o136b2o17bo$5728bo2bo83b2o50b2o16bobo$5719bo9b2o83bo2bo67bobo
            $5718bobo67bo26b2o69bo$5718bobo67bo20b2o$5683b3o33bo15bo52bo20b2o53b3o
            $5704bo29bobo40bo68b2o$5704bo29bobo39bobo60b2o5b2o$5704bo30bo40bobo60b
            2o$5691b3o67bo15bo$5760bobo88b3o$5754b2o5bo100bo$5754b2o93bo5bo5bobo9b
            o16b3o$5675b2o36b2o32b2o29b2o69bo5bo5bobo9bo$5674bobo35bo2bo8b2o21b2o
            29b2o69bo5bo6bo10bo14bo5b2o$5674b2o36bobo4b2o3b2o162bo5b2o$5713bo5b2o
            50b3o77b3o12b2o20bo$5865bo2bo$5769bo5bo8bo81b2o22b3o$5691b2o76bo5bo8bo
            $5690bo2bo11bo63bo5bo8bo$5691b2o12bo113b2o$5705bo21b3o41b3o45b2o2$
            5701b3o3b3o59bo115b2o$5768bobo113bo2bo$5705bo62bo2bo113b2o$5705bo63b2o
            $5705bo$5734bo30bo$5733bobo29bo60b2o$5710b3o21b2o29bo59bo2bo$5685b2o
            119bo18bo2bo$5685b2o21bo5bo90bobo18b2o21b2o4b2o$5696bo11bo5bo90bobo41b
            2o4b2o$5695bobo10bo5bo52b2o37bo28b2o$5695b2o70b2o46bo19b2o24b2o40b2o$
            5710b3o14b2o86bo45b2o40b2o$5727b2o4b2o22b2o56bo57bo$5733b2o22bobo113bo
            $5758bo27bo86bo21b2o$5777b2o6bobo107b2o$5776bo2bo4bo2bo81b3o3b3o$5777b
            2o6b2o93bo$5670b2o10b2o5bo26bo156bo5bobo$5670b2o9bo2bo4bo26bo156bo5bob
            o32b2o$5682b2o5bo26bo22bo39b2o92bo6bo32bobo$5738bobo38b2o132b2o$5738bo
            bo66b2o55b2o$5739bo67b2o54bo2bo$5712b2o149bo2bo$5712b2o150b2o68b2o$
            5705b2o109b2o116b2o$5705b2o59b2o48b2o17b3o$5673b2o52b3o35bo2bo$5672bob
            o91b2o158b2o$5673bo50bo12b2o78b2o107b2o$5723bobo11b2o78b2o54b2o21b3o$
            5723bobo60b2o85b2o$5724bo61b2o2b2o19bo67bo14bo5bo$5682b3o105b2o18bobo
            38bo27bo14bo5bo44b2o$5719b2o7b2o11b2o67bobo38bo27bo14bo5bo2b3o38bobo$
            5718bo2bo5bo2bo10b2o68bo39bo92b2o$5680b2o37b2o7b2o183b2o$5679bo2bo230b
            2o$5667b2o10bobo42bo88bo47b2o$5666bo2bo10bo42bobo82b2o2bobo45bo2bo$
            5667b2o54bobo82b2o2bobo46b2o16b2o$5724bo24b3o61bo21b3o40bo2bo6bo9b2o$
            5879b2o7bo9b2o$5888bo$5665b2o204bo12bo$5664bo78b3o125bo11bobo$5667bo
            108bo94bo11bobo$5665b2o108bobo106bo$5711b2o37b2o15b2o7bo$5711b2o36bo2b
            o14b2o$5740b3o7b2o$5714b3o73b2o29bo32b2o$5659b3o35bo40bo36b2o13b2o2b2o
            25bo32b2o67b3o$5696bobo39bo35bo2bo16b2o25bo$5695bo2bo39bo35bobo$5696b
            2o77bo2$5707b2o157b2o$5702bo3bo2bo55bo50b2o48b2o$5701bobo3b2o56bo50b2o
            $5702b2o61bo$5799bo119b2o$5780b2o17bo119b2o$5751b2o27b2o17bo29b2o$
            5689b2o32b2o26b2o76b2o$5688bo2bo26bo3bo2bo69b3o3b3o54bo$5678bo10b2o26b
            obo3b2o30b2o97bo3bo93b2o$5677bobo37bobo35b2o42bo54bo3bo93bobo$5668b2o
            7bobo38bo80bo54bo78b2o18b2o$5667bobo8bo33bo20b3o63bo25b2o99b2o5b2o$
            5667b2o42bobo110bobo98bo2bo$5672bo38bobo45b2o19b2o42b2o100b2o$5643b2o
            27bo39bo28bo7bo9b2o18bo2bo39b2o$5643b2o27bo31b3o25b2o6bobo5b2o29bo2bo
            38bobo5b2o$5732b2o5bo2bo5b2o5b3o22b2o39b2o5bobo$5702bo5bo31b2o6bo79b2o
            $5702bo5bo117b2o83b3o$5676b3o23bo5bo116bobo25b2o19bo41bo$5671b2o110b2o
            40b2o26b2o19bo34bo5bobo$5671bobo30b3o5b2o58b2o9b2o89bo34bo5bo2bo11b2o$
            5672bobo37b2o44b2o12b2o57b3o75bo6b2o12b2o$5673bo25b3o25bo29bo2bo107b2o
            $5727bo29bo2bo107b2o41b3o24b2o$5697bo5bo23bo30b2o68bo109b2o$5697bo5bo
            106bo16bobo$5646b2o49bo5bo19b3o3b3o77bobo15bobo55b2o$5646b2o148bo13bo
            8bo8bo16b2o8b3o27b2o$5699b3o25bo12b2o53bobo20bobo24b2o91bo$5727bo11bo
            2bo52bobo20bobo117bo$5638b2o14b2o59bo11bo11bobo54bo22bo65bo52bo$5637bo
            2bo13b2o59bo24bo96b3o44bobo$5638b2o75bo15b2o48b2o46b2o53bobo21b2o$
            5621b2o107bobo47bo2bo8bo36b2o2b2o6bo43bo22b2o$5621b2o37b3o43b2o3b3o3b
            3o11bo22b3o24b2o9bo40bobo5bo8bo$5706bobo83bo41b2o5bo8bo$5707bo7bo134bo
            $5646b2o67bo121b3o35bo26b2o$5646b2o67bo158bobo25b2o$5812b2o60bobo$
            5811bo2bo60bo16b2o$5811bobo78b2o$5683b2o78b3o46bo57b2o7b2o$5682bo2bo
            119b2o62bo2bo5bo2bo$5683b2o119bo2bo62b2o7b2o$5628b2o175b2o80b3o$5627bo
            2bo149bo94bo$5628b2o150bo93bobo8bo5bo$5775bo4bo93bobo8bo5bo45b2o$5708b
            2o36b3o26bo99bo9bo5bo45b2o$5708b2o65bo140b2o$5811bo75b3o26b2o11b3o$
            5671b3o137bo140bo$5714b3o44bo16bo32bo140bo$5760bobo15bo173bo$5760bobo
            15bo$5628bo132bo164b2o20b3o3b3o$5628bo19b3o3b3o203bo45b3o17b2o$5628bo
            52bo22b2o11b2o63bo76bobo90bo$5652bo27bobo20bo2bo9bo2bo36bo24bobo38b2o
            35bobo42bo5bo41bo$5596b3o14b2o9b3o3b3o19bo27bobo21b2o11b2o36bobo23bo2b
            o37b2o21b2o13bo43bo5bo41bo$5615bo36bo10bo17bo74bo25b2o27bo22b2o8bo2bo
            33bo22bo5bo$5594bo17bo15bo34bo59b3o37bo47bo21bo2bo8b2o33bobo12b2o49bo$
            5594bo18b2o13bo34bo12b2o7b2o76bo47bo22b2o44bobo2b3o6bobo9b3o37bo$5594b
            o33bo46bo2bo5bo2bo33bo5bo3b2ob2o27bo117bo13bo50bo$5676b2o7b2o34bo5bo3b
            2ob2o78bo$5642b2o77bo5bo31b3o51bobo106b2o$5641bo2bo36bo57b2o72bo2bo
            104bo2bo23bo$5642b2o36bobo40b3o7bo5b2o73b2o105bo2bo22bobo$5638b2o40bob
            o14b3o33bo71b3o114b2o23bo2bo$5637bo2bo4b2o34bo51bo137b2o75b2o$5638b2o
            4bo2bo18bo125b2o47b2o17b2o9b2o28bo$5645b2o18bobo49b2o18b2o16b2o35b2o
            47b2o16bo2bo32b2o4bo$5664bo2bo49b2o18b2o16b2o103b2o33b2o4bo$5641bo11b
            2o10b2o217b2o$5640bobo9bo2bo228b2o$5640bobo10b2o217b2o$5641bo229bobo$
            5765b2o33b3o69bo$5646b2o116bo2bo$5646b2o93b2o21bobo61bo72b2o$5607b2o
            72bo59b2o22bo62bo72b2o$5607b2o72bo113bo32bo$5681bo112bobo$5660bo133bob
            o27b3o3b3o$5660bo126b2o6bo$5660bo126b2o39bo77b2o$5828bo77b2o$5724bo
            103bo65b3o$5611b2o61b2o47bobo$5611b2o61b2o46bo2bo57b3o106bo5bo$5723b2o
            8bo158bo5bo41bo$5733bo158bo5bo41b3o$5733bo209bo$5642bo5b2o244b3o45b2o$
            5641bobo4b2o$5641bobo$5642bo22b2o65b2o$5665b2o28b2o35b2o$5601b2o92b2o
            26b2o$5601bobo119b2o210b2o$5602b2o60b2o268bo2bo$5663bo2bo56b2o210b2o$
            5663bo2bo56b2o$5664b2o274bo$5794bo124bo6b2o11bobo$5793bobo123bo6b2o11b
            obo$5745bo5b3o39bobo123bo20bo$5656bo6b2o80bo48bo$5656bo6b2o80bo$5656bo
            85bo5bo24b2o$5741bobo3bobo22bo2bo$5652b3o3b3o28bo51bobo3bobo23b2o$
            5688bobo42bo8bo5bo$5648b2o6bo31b2o43bo$5641b2o5b2o6bo76bo$5641b2o13bo
            10b2o$5610b2o54bo2bo$5609bobo47b3o4bobo32b2o215b2o$5609b2o56bo33b2o80b
            2o133b2o$5776bo6b2o$5776bo$5776bo$5628b2o25b2o125bo$5628b2o25b2o12bo
            92bo19bo$5669bo91bobo18bo13bo$5669bo90bo2bo8b2o21bobo116b2o$5620b2o
            139b2o9b2o4b3o3b3o9b2o116b2o$5620b2o43b3o3b3o10b3o2$5669bo54b3o5b2o$
            5657bo11bo62b2o$5656bobo10bo$5656bobo21b2o104bo$5657bo22b2o66b2o35bobo
            $5747bo2bo13b2o19bobo$5748b2o13bo2bo19bo15b2o120b2o$5764b2o36b2o119bob
            o$5681bo241b2o$5647b3o30bobo$5680bobo$5681bo94b3o$5649bo$5649bo$5649bo
            28b2o119bo$5678b2o118bobo$5773bo24b2o$5772bobo$5772bobo$5773bo16$5645b
            o$5644bobo$5644bobo10b3o133b2o$5645bo147b2o7$5789b2o$5789b2o$5655b2o$
            5654bobo$5654b2o6$5799b2o$5798bobo$5798b2o1452$7342bo$7343bo$7341b3o
            18$7501bobo$7502b2o$7502bo25$7235bo$7233bobo$7234b2o126$7354bobo$7355b
            2o$7355bo13$4025bobo$4025b2o$4026bo89$3917bo$3917bobo$3917b2o18$7552bo
            $7553bo$7551b3o47$3864bo$3864bobo$3864b2o182$7871bo$7872b2o$7871b2o40$
            7918bo$7919b2o$7918b2o7$3709bo$3709bobo$3709b2o25$7930bo$7931b2o$7930b
            2o53$8060bo$8061b2o$8060b2o70$3627bo$3626bo$3626b3o23$3556bobo$3556b2o
            $3557bo29$8238bo$8239bo$8237b3o108$3384bo$3384bobo$3384b2o12$8430bo$
            8431bo$8429b3o23$3386bo$3385bo$3385b3o25$3313bobo$3313b2o$3314bo852$
            2296bo$2296bobo$2296b2o64$2246bo$2244b2o$2245b2o285$9727bo$9728bo$
            9726b3o504$10220bo$10218bobo$10219b2o133$10398bobo$10399b2o$10399bo
            108$10452bo$10453bo$10451b3o459$674bobo$674b2o$675bo95$655bo$653b2o$
            654b2o14$576bobo$576b2o$577bo380$237bo$236bo$236b3o141$28bo$27bo$27b3o!
        """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
    ),
    lifespan = 23314,
)

data object RPentominoPattern : MethuselahPattern(
    patternName = "R-pentomino",
    seedCellState =
    $$"""
        #N R-pentomino
        #C A methuselah with lifespan 1103.
        #C www.conwaylife.com/wiki/index.php?title=R-pentomino
        x = 3, y = 3, rule = B3/S23
        b2o$2ob$bo!
    """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
    cellStates = mapOf(
        123 to $$"""
            #R -36 -14
            x = 57, y = 36, rule = B3/S23
            46bo$30b2o13bobo$29bobo12bo2b2o$31bo12bobob3o$7b3o34b2ob4o$6b2o2bo25b
            2o7b3o$5bo3b2o25b2o8bo$4bo2b3o$3bo2b2o41b5o$3bo2bo24b3o15b5o$4bo2bo21b
            o3bo14bo2b2o$4bo2bo21bo2b2o14b4o4bo$5b3o21b2o16bo2b2o4bo$47bo2bo5bo$39b
            3o6b3o$38b6o6bo$36bo6bo$2b2o30bobo3b4o$bobo3b2obo22b2o3b2o$3obob4o24b
            5o11bo$4bobo28b2o14bo$4bo10b2o19bo12b3o$3bo11b2o$2bo$2bo2$3b3o$3b3o$2b
            o3bo$2bobo$3b2ob2o3$5bo$6b2o$5b2o!
        """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
        265 to $$"""
            #R -40 -48
            x = 91, y = 106, rule = B3/S23
            69b3o$71bo$70bo28$10b2o$9b2o$11bo7$42bo$41bobo$41b2o$61bo$30b2o17b3ob
            3o4bobo$29bo2bo27b2o$30b2o37bo$68b3o$67b2o2bo$67bob3o$b2o48b3o13b2obo
            b2o$obo48bo2b2o15bo2bo$2o31bo16b2obobo14b6o$32bobo20bo15bo2bo$32bobo15b
            2obobo11b2o3b2o$33bo18b2o2bo10bobo$19b2o33b3o12bo$19b2o33b3o10bobo$64b
            ob3o$63bob2o$11b2o47bo$11b2o46bobobo3bo$61bo2bo$58bo2b2o2b3o$58bo3bo$
            59bo2bo$61bo3b2o$64bo$64bobo$63b2ob2o$64bobo$65bo10$63bobo$64b2o$64bo
            7$90bo$88bobo$89b2o12$44bobo$45b2o$45bo!
        """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
        1103 to $$"""
            #R -240 -258
            x = 501, y = 525, rule = B3/S23
            479b2o$478bobo$480bo28$bo$2o$obo117$180b2o$180bobo$180bo90$265b2o$264b
            o2bo$265bobo$266bo$235bo$234bobo3b2o$235b2o3b2o3$284b3o$271b3o2$293b2o
            $293b2o5$201b2o$200bobo$200b2o31bo$232bobo$232bobo$233bo6bo$219b2o18bo
            bo$219b2o18bobo$240bo2$211b2o$211b2o56b2o$269b2o2$241b3o51b2o$295b2o4$
            307bo$306bobo$283b2o21bobo$283b2o22bo3$295b3o$265bo$264bobo$264bobo$
            265bo2$249b2o$249b2o208$473bo$474b2o$473b2o7$499bo$500bo$498b3o12$454b
            o$455b2o$454b2o!
        """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
    ),
    lifespan = 1103,
)
