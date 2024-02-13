* @set-info :status sat
*NAME:         lseu   
*ROWS:         28
*COLUMNS:      89
*INTEGER:      89
*NONZERO:      309
*BEST SOLN:    1120 (opt)
*LP SOLN:      834.68
*SOURCE:       C. E. Lemke and K. Spielberg
*              Ellis L. Johnson and Uwe H. Suhl 
*              John J. Forrest (IBM)
*APPLICATION:  unknown
*COMMENTS:     pure 0/1 IP
*              
*      
NAME          LSEU
ROWS
 N  R100    
 L  R101    
 L  R102    
 L  R103    
 L  R104    
 L  R105    
 L  R106    
 L  R107    
 L  R108    
 L  R109    
 L  R110    
 L  R111    
 L  R112    
 L  R113    
 L  R114    
 L  R115    
 L  R116    
 L  R117    
 L  R118    
 L  R119    
 L  R120    
 L  R121    
 L  R122    
 L  R123    
 L  R124    
 L  R125    
 L  R126    
 L  R127    
 L  R128    
COLUMNS
    MARK0000  'MARKER'                 'INTORG'
    C101      R100                 7   R119               525
    C101      R120              -525   R122              -525
    C101      R123              -525
    C102      R100                10   R119               500
    C102      R120              -500   R122              -500
    C102      R123              -500
    C103      R100               179   R101                 1
    C103      R119               475   R120              -475
    C103      R124              -475   R125              -475
    C104      R100               186   R101                 1
    C104      R119               475   R120              -475
    C104      R122              -475   R123              -475
    C105      R100               179   R101                 1
    C105      R119               475   R120              -475
    C105      R122              -190   R123              -190
    C105      R124              -285   R125              -285
    C106      R102                 1   R118              -450
    C107      R102                 1   R124              -450
    C107      R125              -450
    C108      R100                 6   R102                 1
    C108      R122              -450   R123              -450
    C109      R102                 1   R122              -165
    C109      R123              -165   R124              -285
    C109      R125              -285
    C110      R102                 1   R124              -150
    C110      R125              -150
    C111      R100               164   R103                 1
    C111      R118              -435
    C112      R100               164   R103                 1
    C112      R124              -435   R125              -435
    C113      R100               170   R103                 1
    C113      R119               435   R120              -435
    C113      R123              -435
    C114      R100               164   R103                 1
    C114      R119               435   R120              -435
    C114      R121              -435
    C115      R100               346   R104                 1
    C115      R124              -435   R125              -435
    C116      R100               346   R104                 1
    C116      R119               435   R120              -435
    C116      R125              -435
    C117      R100               248   R105                 1
    C117      R119               435   R120              -435
    C117      R124              -435   R125              -435
    C118      R100               253   R105                 1
    C118      R119               435   R120              -435
    C118      R122              -435   R123              -435
    C119      R100               248   R105                 1
    C119      R119               435   R120              -435
    C119      R122              -300   R123              -300
    C119      R124              -135   R125              -135
    C120      R100               346   R106                 1
    C120      R118              -435
    C121      R100               346   R106                 1
    C121      R123              -400
    C122      R100               346   R106                 1
    C122      R121              -400
    C123      R100               346   R106                 1
    C123      R124              -100   R125              -100
    C123      R127              -300
    C124      R100               160   R107                 1
    C124      R124              -400   R125              -400
    C125      R100               161   R107                 1
    C125      R122              -400   R123              -400
    C126      R100               160   R107                 1
    C126      R122              -115   R123              -115
    C126      R124              -285   R125              -285
    C127      R100               160   R107                 1
    C127      R119               425   R120              -425
    C127      R125              -425
    C128      R100               161   R107                 1
    C128      R119               425   R120              -425
    C128      R123              -425
    C129      R100               160   R107                 1
    C129      R119               425   R120              -425
    C129      R123              -140   R125              -285
    C130      R100               160   R107                 1
    C130      R124              -100   R125              -100
    C130      R126              -300   R127              -300
    C131      R100               278   R108                 1
    C131      R118              -350
    C132      R100               278   R108                 1
    C132      R124              -350   R125              -350
    C133      R100               278   R108                 1
    C133      R121              -350
    C134      R100                86   R109                 1
    C134      R122              -330   R123              -330
    C135      R100                86   R109                 1
    C135      R126              -330   R127              -330
    C136      R100                86   R109                 1
    C136      R119               330   R120              -330
    C136      R124              -330   R125              -330
    C137      R100                86   R109                 1
    C137      R119               330   R120              -330
    C137      R123              -330
    C138      R100                86   R109                 1
    C138      R119               330   R120              -330
    C138      R121              -330
    C139      R100                86   R119               330
    C139      R120              -330   R122              -330
    C139      R123              -330
    C140      R100               188   R110                 1
    C140      R122              -330   R123              -330
    C141      R100               188   R110                 1
    C141      R119               330   R120              -330
    C141      R124              -330   R125              -330
    C142      R100               188   R110                 1
    C142      R119               330   R120              -330
    C142      R121              -330
    C143      R100                85   R111                 1
    C143      R122              -325   R123              -325
    C144      R100                85   R111                 1
    C144      R126              -325   R127              -325
    C145      R100                85   R111                 1
    C145      R119               325   R120              -325
    C145      R124              -325   R125              -325
    C146      R100                85   R111                 1
    C146      R119               325   R120              -325
    C146      R123              -325
    C147      R100                85   R111                 1
    C147      R119               325   R120              -325
    C147      R121              -325
    C148      R100                78   R112                 1
    C148      R122              -300   R123              -300
    C149      R100                78   R112                 1
    C149      R119               300   R120              -300
    C149      R124              -300   R125              -300
    C150      R100                78   R112                 1
    C150      R119               300   R120              -300
    C150      R121              -300
    C151      R100                78   R112                 1
    C151      R128              -300
    C152      R100                78   R113                 1
    C152      R122              -300   R123              -300
    C153      R100                78   R113                 1
    C153      R126              -300   R127              -300
    C154      R100                78   R113                 1
    C154      R119               300   R120              -300
    C154      R124              -300   R125              -300
    C155      R100                78   R113                 1
    C155      R119               300   R120              -300
    C155      R123              -300
    C156      R100                78   R113                 1
    C156      R119               300   R120              -300
    C156      R121              -300
    C157      R100               171   R114                 1
    C157      R122              -300   R123              -300
    C158      R100               171   R114                 1
    C158      R126              -300   R127              -300
    C159      R100               171   R114                 1
    C159      R119               300   R120              -300
    C159      R123              -300
    C160      R100               171   R114                 1
    C160      R119               300   R120              -300
    C160      R121              -300
    C161      R100               163   R115                 1
    C161      R119               285   R120              -285
    C161      R124              -285   R125              -285
    C162      R100               163   R115                 1
    C162      R119               285   R120              -285
    C162      R122              -285   R123              -285
    C163      R100               163   R115                 1
    C163      R128              -285
    C164      R100                69   R116                 1
    C164      R119               265   R120              -265
    C164      R124              -265   R125              -265
    C165      R100                69   R116                 1
    C165      R119               265   R120              -265
    C165      R122              -265   R123              -265
    C166      R100               183   R117                 1
    C166      R118              -230
    C167      R100               183   R117                 1
    C167      R124              -230   R125              -230
    C168      R100               183   R117                 1
    C168      R119               230   R120              -230
    C168      R125              -230
    C169      R100               183   R117                 1
    C169      R119               230   R120              -230
    C169      R123              -230
    C170      R100                49   R119               190
    C170      R120              -190   R122              -190
    C170      R123              -190
    C171      R100               183   R117                 1
    C172      R100               258   R118              -200
    C173      R100               517   R118              -400
    C174      R100               250   R126              -200
    C174      R127              -200
    C175      R100               500   R126              -400
    C175      R127              -400
    C176      R100               250   R127              -200
    C177      R100               500   R127              -400
    C178      R100               159   R119               200
    C178      R120              -200   R124              -200
    C178      R125              -200
    C179      R100               318   R119               400
    C179      R120              -400   R124              -400
    C179      R125              -400
    C180      R100               159   R119               200
    C180      R120              -200   R125              -200
    C181      R100               318   R119               400
    C181      R120              -400   R125              -400
    C182      R100               159   R119               200
    C182      R120              -200   R122              -200
    C182      R123              -200
    C183      R100               318   R119               400
    C183      R120              -400   R122              -400
    C183      R123              -400
    C184      R100               159   R119               200
    C184      R120              -200   R123              -200
    C185      R100               318   R119               400
    C185      R120              -400   R123              -400
    C186      R100               114   R119               200
    C186      R120              -200   R121              -200
    C187      R100               228   R119               400
    C187      R120              -400   R121              -400
    C188      R100               159   R128              -200
    C189      R100               318   R128              -400
    MARK0001  'MARKER'                 'INTEND'
RHS
    RHS       R101                 1   R102                 1
    RHS       R103                 1   R104                 1
    RHS       R105                 1   R106                 1
    RHS       R107                 1   R108                 1
    RHS       R109                 1   R110                 1
    RHS       R111                 1   R112                 1
    RHS       R113                 1   R114                 1
    RHS       R115                 1   R116                 1
    RHS       R117                 1   R118              -190
    RHS       R119              2700   R120             -2600
    RHS       R121              -630   R122              -900
    RHS       R123             -1656   R124              -335
    RHS       R125             -1026   R126              -150
    RHS       R127              -500   R128              -270
BOUNDS
 UP ONE       C101                 1
 UP ONE       C102                 1
 UP ONE       C103                 1
 UP ONE       C104                 1
 UP ONE       C105                 1
 UP ONE       C106                 1
 UP ONE       C107                 1
 UP ONE       C108                 1
 UP ONE       C109                 1
 UP ONE       C110                 1
 UP ONE       C111                 1
 UP ONE       C112                 1
 UP ONE       C113                 1
 UP ONE       C114                 1
 UP ONE       C115                 1
 UP ONE       C116                 1
 UP ONE       C117                 1
 UP ONE       C118                 1
 UP ONE       C119                 1
 UP ONE       C120                 1
 UP ONE       C121                 1
 UP ONE       C122                 1
 UP ONE       C123                 1
 UP ONE       C124                 1
 UP ONE       C125                 1
 UP ONE       C126                 1
 UP ONE       C127                 1
 UP ONE       C128                 1
 UP ONE       C129                 1
 UP ONE       C130                 1
 UP ONE       C131                 1
 UP ONE       C132                 1
 UP ONE       C133                 1
 UP ONE       C134                 1
 UP ONE       C135                 1
 UP ONE       C136                 1
 UP ONE       C137                 1
 UP ONE       C138                 1
 UP ONE       C139                 1
 UP ONE       C140                 1
 UP ONE       C141                 1
 UP ONE       C142                 1
 UP ONE       C143                 1
 UP ONE       C144                 1
 UP ONE       C145                 1
 UP ONE       C146                 1
 UP ONE       C147                 1
 UP ONE       C148                 1
 UP ONE       C149                 1
 UP ONE       C150                 1
 UP ONE       C151                 1
 UP ONE       C152                 1
 UP ONE       C153                 1
 UP ONE       C154                 1
 UP ONE       C155                 1
 UP ONE       C156                 1
 UP ONE       C157                 1
 UP ONE       C158                 1
 UP ONE       C159                 1
 UP ONE       C160                 1
 UP ONE       C161                 1
 UP ONE       C162                 1
 UP ONE       C163                 1
 UP ONE       C164                 1
 UP ONE       C165                 1
 UP ONE       C166                 1
 UP ONE       C167                 1
 UP ONE       C168                 1
 UP ONE       C169                 1
 UP ONE       C170                 1
 UP ONE       C171                 1
 UP ONE       C172                 1
 UP ONE       C173                 1
 UP ONE       C174                 1
 UP ONE       C175                 1
 UP ONE       C176                 1
 UP ONE       C177                 1
 UP ONE       C178                 1
 UP ONE       C179                 1
 UP ONE       C180                 1
 UP ONE       C181                 1
 UP ONE       C182                 1
 UP ONE       C183                 1
 UP ONE       C184                 1
 UP ONE       C185                 1
 UP ONE       C186                 1
 UP ONE       C187                 1
 UP ONE       C188                 1
 UP ONE       C189                 1
ENDATA
