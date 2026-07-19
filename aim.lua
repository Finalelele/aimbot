-- ===== INITIALIZATION =====
local Rayfield = loadstring(game:HttpGet("https://raw.githubusercontent.com/SiriusSoftwareLtd/Rayfield/main/source.lua"))()

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local VirtualInputManager = game:GetService("VirtualInputManager")
local VRService = game:GetService("VRService")
local GuiService = game:GetService("GuiService")
local UserInputService = game:GetService("UserInputService")
local CoreGui = game:GetService("CoreGui")
local LocalPlayer = Players.LocalPlayer
local Camera = workspace.CurrentCamera

local function generateRandomName()
    local chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    local length = math.random(10, 16)
    local str = ""
    for i = 1, length do
        local rand = math.random(1, #chars)
        str = str .. string.sub(chars, rand, rand)
    end
    return str
end

local LASER_NAME = generateRandomName()
local ESP_SUFFIX = "_" .. generateRandomName()

local Options = {
    AimbotEnabled = false,
    AutoShoot = false,      
    TeamCheck = false,      
    AntiFriends = false,  
    UseFOV = false,         
    AimFOV = 150,           
    ShowFOV = true,         
    Smoothness = 0,        
    LaserTransparency = 0, 
    MaxDistance = 150,     
    Cooldown = 0.05,        
    TargetLock = false,     
    TargetPart = "Head", 
    HitboxSilentAim = false,
    HitboxSize = 10,
    HoldToAim = false,
    WallCheck = true,
    Whitelist = {},
    EspHighlight = false,
    EspNames = false,
    EspHealth = false,
    EspDistance = false,
    EspTracers = false,
    EspTeam = false,
    ShowEspIcon = false,
    EspHitbox = false,
    EspHitboxTransparency = 0.85
}

local FriendsCache = {}
local WhitelistDropdown = nil
local ActiveEspObjects = {} 
local ActiveTracers = {}    
local isAimKeyDown = false 
local CurrentTarget = nil
local laserContainer = nil
local OriginalSizes = setmetatable({}, {__mode = "k"})

-- Глобальные кэши для текущего кадра (Оптимизация Team Check)
local Cache_MyTeam = nil
local Cache_MyNeutral = false

local mainRaycastParams = RaycastParams.new()
mainRaycastParams.FilterType = Enum.RaycastFilterType.Exclude
local mainIgnoreTable = {}

local wallCheckRaycastParams = RaycastParams.new()
wallCheckRaycastParams.FilterType = Enum.RaycastFilterType.Exclude
local wallCheckIgnoreTable = {}

UserInputService.InputBegan:Connect(function(input, gameProcessed)
    if input.UserInputType == Enum.UserInputType.MouseButton2 or input.UserInputType == Enum.UserInputType.Touch then
        isAimKeyDown = true
    end
end)

UserInputService.InputEnded:Connect(function(input, gameProcessed)
    if input.UserInputType == Enum.UserInputType.MouseButton2 or input.UserInputType == Enum.UserInputType.Touch then
        isAimKeyDown = false
        if Options.HoldToAim then
            CurrentTarget = nil 
        end
    end
end)

-- ===== ESP SYSTEM =====
local function getHealth(character, humanoid)
    if not humanoid then return 0, 100 end
    local health = humanoid.Health
    local maxHealth = humanoid.MaxHealth
    
    local attrHealth = character:GetAttribute("Health") or character:GetAttribute("HP")
    local attrMaxHealth = character:GetAttribute("MaxHealth") or character:GetAttribute("MaxHP")
    if attrHealth and type(attrHealth) == "number" then
        health = attrHealth
        if attrMaxHealth and type(attrMaxHealth) == "number" then
            maxHealth = attrMaxHealth
        end
    end
    
    local valHealth = character:FindFirstChild("Health") or character:FindFirstChild("HP")
    if valHealth and (valHealth:IsA("NumberValue") or valHealth:IsA("IntValue")) then
        health = valHealth.Value
        local valMax = character:FindFirstChild("MaxHealth") or character:FindFirstChild("MaxHP")
        if valMax and (valMax:IsA("NumberValue") or valMax:IsA("IntValue")) then
            maxHealth = valMax.Value
        end
    end
    
    return health, maxHealth
end

local function getSpecificHitbox(character, targetName)
    if not character then return nil end
    
    if targetName == "Head" then
        local headNames = {"HeadHB", "head_hitbox", "Head_HB", "FakeHead", "Head"}
        for _, name in ipairs(headNames) do
            local part = character:FindFirstChild(name)
            if part and part:IsA("BasePart") then
                return part
            end
        end
    else
        local part = character:FindFirstChild(targetName)
        if part and part:IsA("BasePart") then
            return part
        end
        
        for _, child in ipairs(character:GetChildren()) do
            if child:IsA("BasePart") and child.Name:lower() == targetName:lower() then
                return child
            end
        end
    end
    
    local hrp = character:FindFirstChild("HumanoidRootPart")
    if hrp then return hrp end
    
    for _, child in ipairs(character:GetChildren()) do
        if child:IsA("Humanoid") then
            local root = child.RootPart
            if root then return root end
        end
    end
    
    local torso = character:FindFirstChild("Torso") or character:FindFirstChild("UpperTorso")
    if torso then return torso end
    return nil
end

local function createEsp(player)
    if player == LocalPlayer then return end
    if ActiveEspObjects[player] then return end 

    local folder = Instance.new("Folder")
    folder.Name = player.Name .. ESP_SUFFIX 
    folder.Parent = CoreGui

    local highlight = Instance.new("Highlight")
    highlight.Name = generateRandomName()
    highlight.OutlineColor = Color3.fromRGB(255, 255, 255)
    highlight.FillTransparency = 0.5
    highlight.OutlineTransparency = 0
    highlight.Enabled = false
    highlight.Parent = folder

    local billboard = Instance.new("BillboardGui")
    billboard.Name = generateRandomName()
    billboard.Size = UDim2.new(0, 200, 0, 150) 
    billboard.AlwaysOnTop = true
    billboard.StudsOffset = Vector3.new(0, 3.5, 0) 
    billboard.MaxDistance = Options.MaxDistance + 50 
    billboard.ResetOnSpawn = false
    billboard.Enabled = false
    billboard.Parent = folder

    local iconImage = Instance.new("ImageLabel")
    iconImage.AnchorPoint = Vector2.new(0.5, 0)
    iconImage.Position = UDim2.new(0.5, 0, 0, 0)
    iconImage.Size = UDim2.new(0, 40, 0, 40) 
    iconImage.BackgroundTransparency = 1
    iconImage.Image = "rbxthumb://type=AvatarHeadShot&id=" .. player.UserId .. "&w=150&h=150"
    iconImage.Visible = false
    
    local corner = Instance.new("UICorner")
    corner.CornerRadius = UDim.new(1, 0)
    corner.Parent = iconImage
    iconImage.Parent = billboard

    local textLabel = Instance.new("TextLabel")
    textLabel.AnchorPoint = Vector2.new(0.5, 0)
    textLabel.Position = UDim2.new(0.5, 0, 0, 45) 
    textLabel.Size = UDim2.new(1, 0, 0, 30) 
    textLabel.BackgroundTransparency = 1
    textLabel.TextColor3 = Color3.fromRGB(255, 255, 255)
    textLabel.TextStrokeTransparency = 0
    textLabel.TextSize = 12 
    textLabel.TextScaled = false 
    textLabel.Font = Enum.Font.SourceSansBold
    textLabel.Text = ""
    textLabel.Visible = false
    textLabel.Parent = billboard

    local boxAdornment = Instance.new("BoxHandleAdornment")
    boxAdornment.Name = generateRandomName()
    boxAdornment.AlwaysOnTop = true
    boxAdornment.ZIndex = 5
    boxAdornment.Transparency = Options.EspHitboxTransparency
    boxAdornment.Color3 = Color3.fromRGB(0, 255, 255)
    boxAdornment.Visible = false
    boxAdornment.Adornee = nil
    boxAdornment.Parent = folder 

    local selectionBox = Instance.new("SelectionBox")
    selectionBox.Name = generateRandomName()
    selectionBox.Color3 = Color3.fromRGB(0, 255, 255) 
    selectionBox.Transparency = 0.3
    selectionBox.Adornee = nil
    selectionBox.Parent = folder 

    ActiveEspObjects[player] = {
        Folder = folder,
        Highlight = highlight,
        Billboard = billboard,
        Label = textLabel,
        IconImage = iconImage,
        BoxAdornment = boxAdornment,
        SelectionBox = selectionBox,
        Cache = {
            Health = -1,
            Dist = -1
        }
    }
    
    if Drawing then
        pcall(function()
            local line = Drawing.new("Line")
            line.Color = Color3.fromRGB(255, 0, 0)
            line.Thickness = 1.0
            line.Transparency = 1
            line.Visible = false
            ActiveTracers[player] = line
        end)
    end
end

-- Мягкое скрытие ESP вместо дестроя (решает проблему спама)
local function hideEsp(player)
    local esp = ActiveEspObjects[player]
    if esp then
        if esp.Highlight.Enabled then esp.Highlight.Enabled = false end
        if esp.Billboard.Enabled then esp.Billboard.Enabled = false end
        if esp.BoxAdornment.Visible then esp.BoxAdornment.Visible = false end
        if esp.BoxAdornment.Adornee ~= nil then esp.BoxAdornment.Adornee = nil end
        if esp.SelectionBox.Adornee ~= nil then esp.SelectionBox.Adornee = nil end
    end
    local tracer = ActiveTracers[player]
    if tracer and tracer.Visible then
        tracer.Visible = false
    end
end

-- Полное удаление (вызывается ТОЛЬКО при выходе игрока или закрытии скрипта)
local function removeEsp(player)
    if ActiveEspObjects[player] then
        pcall(function() ActiveEspObjects[player].Folder:Destroy() end)
        ActiveEspObjects[player] = nil
    end
    if ActiveTracers[player] then
        pcall(function() ActiveTracers[player]:Remove() end)
        ActiveTracers[player] = nil
    end
    if player.Character then
        for part, orig in pairs(OriginalSizes) do
            if part and part.Parent and part:IsDescendantOf(player.Character) then
                part.Size = orig.Size
                part.CanCollide = orig.CanCollide
                part.Transparency = orig.Transparency
            end
        end
    end
end

local function cacheFriendStatus(player)
    if player == LocalPlayer then return end
    pcall(function()
        local isFriend = LocalPlayer:IsFriendsWith(player.UserId)
        FriendsCache[player.Name] = isFriend
    end)
end

local function getPlayerNames()
    local names = {}
    for _, p in ipairs(Players:GetPlayers()) do
        if p ~= LocalPlayer then table.insert(names, p.Name) end
    end
    return names
end

for _, p in ipairs(Players:GetPlayers()) do 
    cacheFriendStatus(p) 
    createEsp(p)
end

Players.PlayerAdded:Connect(function(player)
    cacheFriendStatus(player)
    createEsp(player)
    if WhitelistDropdown then
        pcall(function()
            WhitelistDropdown:Refresh(getPlayerNames(), true)
        end)
    end
end)

Players.PlayerRemoving:Connect(function(player)
    FriendsCache[player.Name] = nil
    Options.Whitelist[player.Name] = nil
    removeEsp(player)
    if WhitelistDropdown then
        pcall(function()
            WhitelistDropdown:Refresh(getPlayerNames(), true)
        end)
    end
end)

local LASER_COLOR = Color3.fromRGB(0, 255, 255)
local scriptId = tick()
shared.TriggerbotScriptId = scriptId

local lastShot = 0
local lastHitboxUpdate = 0
local wasHitboxActive = false 
local isRobloxMenuOpen = false

GuiService.MenuOpened:Connect(function()
    isRobloxMenuOpen = true
    CurrentTarget = nil
end)
GuiService.MenuClosed:Connect(function()
    isRobloxMenuOpen = false
end)

local inVR = false
pcall(function()
    if VRService.VREnabled then 
        inVR = true 
    else
        local char = LocalPlayer.Character
        if char and char:GetAttribute("InVR") == true then 
            inVR = true 
        end
    end
end)

local FOVCircle = nil
if not inVR and Drawing then
    pcall(function()
        FOVCircle = Drawing.new("Circle")
        FOVCircle.Visible = false
        FOVCircle.Thickness = 1
        FOVCircle.NumSides = 32 
        FOVCircle.Radius = Options.AimFOV
        FOVCircle.Filled = false
        FOVCircle.Color = LASER_COLOR
        FOVCircle.Transparency = 0.5
    end)
end

local Window = Rayfield:CreateWindow({
	Name = "Aimbot Universal",
	ScriptID = "sid_ca0y2a9a6103",
	Icon = "loader",
	LoadingTitle = "Loading Script...",
	LoadingSubtitle = "by Finalelele",
	ShowText = "Rayfield",
	Theme = "Ocean",
	ToggleUIKeybind = "K",
	DisableRayfieldPrompts = false,
	DisableBuildWarnings = false,
	ConfigurationSaving = {
		Enabled = true,
		FolderName = "FinaleleleAimbot",
		FileName = "Config"
	},
	Discord = {
		Enabled = false,
		Invite = "noinvitelink",
		RememberJoins = true
	},
	KeySystem = false,
	KeySettings = {
		Title = "Untitled",
		Subtitle = "Key System",
		Note = "No method of obtaining the key is provided",
		FileName = "Key",
		SaveKey = true,
		GrabKeyFromSite = false,
		Key = {"Hello"}
	}
})

-- ===== MAIN TAB =====
local Tab = Window:CreateTab("Main Settings", "list")
local EspTab = Window:CreateTab("ESP", "eye") 

if not inVR then
    Tab:CreateToggle({
        Name = "Enable Aim Lock",
        CurrentValue = false,
        Flag = "Aimbot_Toggle",
        Callback = function(Value)
            Options.AimbotEnabled = Value
            if not Value then CurrentTarget = nil end
        end,
    })
    
    Tab:CreateToggle({
        Name = "Hold to Aim",
        CurrentValue = false,
        Flag = "HoldToAim_Toggle",
        Callback = function(Value) Options.HoldToAim = Value end
    })
end

Tab:CreateToggle({
    Name = "Wall Check",
    CurrentValue = true,
    Flag = "WallCheck_Toggle",
    Callback = function(Value) Options.WallCheck = Value end
})

Tab:CreateToggle({
    Name = "Hitbox Silent Aim",
    CurrentValue = false,
    Flag = "HitboxSilent_Toggle",
    Callback = function(Value) Options.HitboxSilentAim = Value end,
})

Tab:CreateToggle({
    Name = "Triggerbot",
    CurrentValue = false,
    Flag = "AutoShoot_Toggle",
    Callback = function(Value) Options.AutoShoot = Value end,
})

if not inVR then
    Tab:CreateToggle({
        Name = "Use FOV",
        CurrentValue = false,
        Flag = "UseFOV_Toggle",
        Callback = function(Value) Options.UseFOV = Value end
    })

    Tab:CreateToggle({
        Name = "Show FOV",
        CurrentValue = true,
        Flag = "ShowFOV_Toggle",
        Callback = function(Value) Options.ShowFOV = Value end,
    })
end

Tab:CreateToggle({
    Name = "Team Check",
    CurrentValue = false, 
    Flag = "TeamCheck_Toggle",
    Callback = function(Value) Options.TeamCheck = Value end
})

Tab:CreateToggle({
    Name = "Anti-Friends",
    CurrentValue = false,
    Flag = "AntiFriends_Toggle",
    Callback = function(Value) Options.AntiFriends = Value end
})

if not inVR then
    Tab:CreateToggle({
        Name = "Target Lock",
        CurrentValue = false,
        Flag = "TargetLock_Toggle",
        Callback = function(Value)
            Options.TargetLock = Value
            if not Value then CurrentTarget = nil end
        end,
    })
end

-- ===== MAIN TAB 2 =====
if not inVR then
    Tab:CreateSlider({
        Name = "FOV Radius",
        Range = {30, 600}, 
        Increment = 10,
        Suffix = " px",
        CurrentValue = 150, 
        Flag = "FOV_Slider", 
        Callback = function(Value)
            Options.AimFOV = Value
            if FOVCircle then FOVCircle.Radius = Value end 
        end,
    })

    Tab:CreateSlider({
        Name = "Aim Smoothness",
        Range = {0, 95}, 
        Increment = 1,
        Suffix = "%",
        CurrentValue = 0,
        Flag = "Smooth_Slider", 
        Callback = function(Value) Options.Smoothness = Value / 100 end,
    })
end

Tab:CreateSlider({
    Name = "Silent Aim Width",
    Range = {1, 30},
    Increment = 1,
    Suffix = " studs",
    CurrentValue = 10,
    Flag = "HitboxSize_Slider",
    Callback = function(Value) Options.HitboxSize = Value end
})

Tab:CreateSlider({
    Name = "Fire Rate",
    Range = {0, 0.50}, 
    Increment = 0.01,     
    Suffix = "s",         
    CurrentValue = 0.05, 
    Flag = "Cooldown_Slider", 
    Callback = function(Value) Options.Cooldown = Value end,
})

Tab:CreateSlider({
    Name = "Max Distance",
    Range = {10, 500},
    Increment = 5,
    Suffix = " studs",
    CurrentValue = 150, 
    Flag = "Distance_Slider", 
    Callback = function(Value) Options.MaxDistance = Value end
})

Tab:CreateSlider({
    Name = "Laser Transparency",
    Range = {0, 100},
    Increment = 1,
    Suffix = "%",
    CurrentValue = 0,
    Flag = "Laser_Trans_Slider", 
    Callback = function(Value)
        Options.LaserTransparency = Value / 100
        if shared.LaserPart then shared.LaserPart.Transparency = Options.LaserTransparency end
    end,
})

Tab:CreateDropdown({
    Name = "Target Hitbox",
    Options = {"Head", "HumanoidRootPart"},
    CurrentOption = {"Head"},
    MultipleOptions = false,
    Flag = "TargetPart_Dropdown",
    Callback = function(TargetList) Options.TargetPart = TargetList[1] or "Head" end
})

WhitelistDropdown = Tab:CreateDropdown({
    Name = "Player Whitelist",
    Options = getPlayerNames(),
    CurrentOption = {},
    MultipleOptions = true,
    Flag = "Whitelist_Drop",
    Callback = function(OptionsList)
        Options.Whitelist = {}
        for _, name in ipairs(OptionsList) do 
            Options.Whitelist[name] = true 
        end
    end,
})

-- ===== ESP TAB =====
EspTab:CreateSection("ESP Visuals")

EspTab:CreateToggle({
    Name = "Chams",
    CurrentValue = false,
    Flag = "Esp_Highlight",
    Callback = function(Value) Options.EspHighlight = Value end,
})

EspTab:CreateToggle({
    Name = "Show Player Names",
    CurrentValue = false,
    Flag = "Esp_Names",
    Callback = function(Value) Options.EspNames = Value end,
})

EspTab:CreateToggle({
    Name = "Show Health Bar",
    CurrentValue = false,
    Flag = "Esp_Health",
    Callback = function(Value) Options.EspHealth = Value end,
})

EspTab:CreateToggle({
    Name = "Show Distance",
    CurrentValue = false,
    Flag = "Esp_Distance",
    Callback = function(Value) Options.EspDistance = Value end,
})

EspTab:CreateToggle({
    Name = "Show Tracers",
    CurrentValue = false,
    Flag = "Esp_Tracers",
    Callback = function(Value) Options.EspTracers = Value end,
})

EspTab:CreateToggle({
    Name = "Show Player Icon", 
    CurrentValue = false,
    Flag = "Esp_Icon",
    Callback = function(Value) Options.ShowEspIcon = Value end,
})

EspTab:CreateToggle({
    Name = "Show Hitbox Box", 
    CurrentValue = false,
    Flag = "Esp_Hitbox",
    Callback = function(Value) Options.EspHitbox = Value end,
})

EspTab:CreateSlider({
    Name = "Hitbox ESP Transparency",
    Range = {0, 100},
    Increment = 1,
    Suffix = "%",
    CurrentValue = 85,
    Flag = "Esp_Hitbox_Trans",
    Callback = function(Value) Options.EspHitboxTransparency = Value / 100 end,
})

EspTab:CreateToggle({
    Name = "Show Team ESP",
    CurrentValue = false,
    Flag = "Esp_Team_Toggle",
    Callback = function(Value) Options.EspTeam = Value end,
})

-- ===== LOGIC & RENDERING =====

if shared.LaserPart then pcall(function() shared.LaserPart:Destroy() end) end
laserContainer = Instance.new("Part")
laserContainer.Name = LASER_NAME 
laserContainer.Anchored = true
laserContainer.CanCollide = false
laserContainer.CanQuery = false
laserContainer.CanTouch = false
laserContainer.CastShadow = false 
laserContainer.Material = Enum.Material.Plastic
laserContainer.Color = LASER_COLOR
laserContainer.Transparency = Options.LaserTransparency
laserContainer.Parent = CoreGui
shared.LaserPart = laserContainer

local function drawLaser(startPos, endPos)
    if laserContainer and laserContainer.Parent then
        local distance = (startPos - endPos).Magnitude
        if distance > 0 then
            local newSize = Vector3.new(0.04, 0.04, distance)
            local newCFrame = CFrame.lookAt(startPos, endPos) * CFrame.new(0, 0, -distance/2)
            if laserContainer.Size ~= newSize then
                laserContainer.Size = newSize
            end
            if laserContainer.CFrame ~= newCFrame then
                laserContainer.CFrame = newCFrame
            end
        else
            local zeroSize = Vector3.new(0, 0, 0)
            if laserContainer.Size ~= zeroSize then
                laserContainer.Size = zeroSize
            end
        end
    end
end

local function isVisible(originPos, targetPart, character)
    if not Options.WallCheck then return true end

    table.clear(wallCheckIgnoreTable)
    if laserContainer then table.insert(wallCheckIgnoreTable, laserContainer) end
    if character then table.insert(wallCheckIgnoreTable, character) end
    
    wallCheckRaycastParams.FilterDescendantsInstances = wallCheckIgnoreTable
    
    local direction = targetPart.Position - originPos
    local result = workspace:Raycast(originPos, direction, wallCheckRaycastParams)
    
    if not result then return true end
    if result.Instance:IsDescendantOf(targetPart.Parent) then return true end
    return false
end

-- Твоя оригинальная логика Team Check (нейтралы считаются союзниками)
local function isAllyFast(player)
    if not player then return false end
    
    if player.Neutral == true and Cache_MyNeutral == true then
        return true
    end
    
    if player.Team ~= nil and Cache_MyTeam ~= nil and player.Team == Cache_MyTeam then 
        return true 
    end
    
    return false
end

local function checkValidTarget(model)
    local player = Players:GetPlayerFromCharacter(model) or Players:FindFirstChild(model.Name)
    if player and player ~= LocalPlayer then
        if Options.TeamCheck and isAllyFast(player) then
            return nil 
        end
        if Options.AntiFriends and FriendsCache[player.Name] then return nil end
        if Options.Whitelist[player.Name] then return nil end 

        local humanoid = model:FindFirstChildOfClass("Humanoid")
        if humanoid then
            local currentHp = getHealth(model, humanoid)
            if currentHp > 0 then
                if model:FindFirstChild("ProtectionHighlight") then return nil end
                return player
            end
        end
    end
    return nil
end

local function getClosestEnemy(originPos, character)
    if isRobloxMenuOpen then 
        CurrentTarget = nil
        return nil 
    end

    if Options.HoldToAim and not isAimKeyDown then
        CurrentTarget = nil
        return nil
    end

    if CurrentTarget and CurrentTarget.Parent and checkValidTarget(CurrentTarget.Parent) then
        local isDist = (originPos - CurrentTarget.Position).Magnitude <= Options.MaxDistance
        local isVisibleNow = isVisible(originPos, CurrentTarget, character) 
        if isDist and isVisibleNow then
            if Options.TargetLock then
                return CurrentTarget
            end
        else
            CurrentTarget = nil
        end
    else
        CurrentTarget = nil
    end

    local closestTarget = nil
    local shortestDistance = Options.MaxDistance 
    local halfX = Camera.ViewportSize.X * 0.5
    local halfY = Camera.ViewportSize.Y * 0.5
    local aimFovSq = Options.AimFOV * Options.AimFOV
    
    for _, player in ipairs(Players:GetPlayers()) do
        if player ~= LocalPlayer and player.Character then
            local targetHitbox = getSpecificHitbox(player.Character, Options.TargetPart)
            
            if targetHitbox and checkValidTarget(player.Character) then
                local distance = (originPos - targetHitbox.Position).Magnitude
                if distance < shortestDistance then
                    local inFOV = true
                    
                    if Options.UseFOV and not inVR and CurrentTarget ~= targetHitbox then
                        local screenPos, onScreen = Camera:WorldToViewportPoint(targetHitbox.Position)
                        if onScreen and screenPos.Z > 0 then
                            local dx = screenPos.X - halfX
                            local dy = screenPos.Y - halfY
                            inFOV = (dx * dx + dy * dy) <= aimFovSq
                        else
                            inFOV = false
                        end
                    end

                    if inFOV then
                        if isVisible(originPos, targetHitbox, character) then
                            shortestDistance = distance
                            closestTarget = targetHitbox
                        end
                    end
                end
            end
        end
    end

    if closestTarget then
        CurrentTarget = CurrentTarget or closestTarget
    end
    
    return CurrentTarget
end

-- ТВОЯ ОПТИМИЗАЦИЯ: Используется строго GetChildren()!
local function updateHitboxes(forceReset)
    local currentSize = Options.HitboxSize or 10
    local hitboxAim = Options.HitboxSilentAim and not forceReset
    local targetSize = Vector3.new(currentSize, currentSize, currentSize)
    
    for _, v in ipairs(Players:GetPlayers()) do
        if v ~= LocalPlayer and v.Character then
            local isEnemy = true
            if Options.TeamCheck and isAllyFast(v) then isEnemy = false end
            if Options.AntiFriends and FriendsCache[v.Name] then isEnemy = false end
            if Options.Whitelist[v.Name] then isEnemy = false end

            local activeHitboxes = {}
            if hitboxAim and isEnemy then
                local headPart = getSpecificHitbox(v.Character, "Head")
                if headPart then activeHitboxes[headPart] = true end

                local hrp = v.Character:FindFirstChild("HumanoidRootPart")
                if hrp and hrp ~= headPart then activeHitboxes[hrp] = true end
            end

            for _, child in ipairs(v.Character:GetChildren()) do
                if child:IsA("BasePart") then
                    if activeHitboxes[child] then
                        if not OriginalSizes[child] then
                            OriginalSizes[child] = {
                                Size = child.Size, 
                                Transparency = child.Transparency, 
                                CanCollide = child.CanCollide
                            }
                        end
                        if child.CanCollide ~= false then child.CanCollide = false end
                        if child.Transparency ~= 10 then child.Transparency = 10 end
                        if child.Size ~= targetSize then child.Size = targetSize end
                    else
                        if OriginalSizes[child] then
                            local orig = OriginalSizes[child]
                            if child.CanCollide ~= orig.CanCollide then child.CanCollide = orig.CanCollide end
                            if child.Transparency ~= orig.Transparency then child.Transparency = orig.Transparency end
                            if child.Size ~= orig.Size then child.Size = orig.Size end
                        end
                    end
                end
            end
        end
    end
end

local renderStepName = "CombatHubRender_" .. tostring(scriptId)

local function onRenderStep()
    if shared.TriggerbotScriptId ~= scriptId then
        if laserContainer then pcall(function() laserContainer:Destroy() end) end
        if FOVCircle then pcall(function() FOVCircle:Remove() end) end 
        for p, _ in pairs(ActiveEspObjects) do removeEsp(p) end
        RunService:UnbindFromRenderStep(renderStepName)
        return
    end

    Cache_MyTeam = LocalPlayer.Team
    Cache_MyNeutral = (LocalPlayer.Neutral == true)

    if Options.HitboxSilentAim then
        wasHitboxActive = true
        if tick() - lastHitboxUpdate > 0.5 then
            lastHitboxUpdate = tick()
            task.spawn(function() updateHitboxes(false) end)
        end
    elseif wasHitboxActive then
        wasHitboxActive = false
        task.spawn(function() updateHitboxes(true) end)
    end

    local character = LocalPlayer.Character
    local rayOrigin = Camera.CFrame.Position
    local rayDirection = Camera.CFrame.LookVector * Options.MaxDistance
    
    local targetHitbox = nil

    if Options.AimbotEnabled or Options.AutoShoot then
        targetHitbox = getClosestEnemy(rayOrigin, character)
    end

    if not inVR then
        if FOVCircle then
            if (Options.AimbotEnabled or Options.AutoShoot) and Options.UseFOV and Options.ShowFOV then
                local center = Camera.ViewportSize * 0.5
                if FOVCircle.Position ~= center then
                    FOVCircle.Position = center
                end
                if not FOVCircle.Visible then FOVCircle.Visible = true end
            else
                if FOVCircle.Visible then FOVCircle.Visible = false end
            end
        end

        if targetHitbox and Options.AimbotEnabled and not isRobloxMenuOpen then
            local canAim = true
            if Options.HoldToAim and not isAimKeyDown then
                canAim = false
            end

            if canAim then
                if not Options.HitboxSilentAim then
                    local targetPosition = targetHitbox.Position
                    local lookCFrame = CFrame.lookAt(Camera.CFrame.Position, targetPosition)
                    if Options.Smoothness == 0 then
                        Camera.CFrame = lookCFrame
                    else
                        local lerpFactor = math.clamp(1 / ((Options.Smoothness * 10) + 1), 0.05, 1)
                        Camera.CFrame = Camera.CFrame:Lerp(lookCFrame, lerpFactor)
                    end
                else
                    rayDirection = (targetHitbox.Position - rayOrigin).Unit * Options.MaxDistance
                end
            end 
        end
    end

    table.clear(mainIgnoreTable)
    if laserContainer then table.insert(mainIgnoreTable, laserContainer) end
    if character then table.insert(mainIgnoreTable, character) end
    mainRaycastParams.FilterDescendantsInstances = mainIgnoreTable

    local raycastResult = nil
    local triggerbotResult = nil
    local endPosition = rayOrigin + rayDirection

    if Options.AutoShoot or laserContainer.Transparency < 1 then
        raycastResult = workspace:Raycast(rayOrigin, rayDirection, mainRaycastParams)
        if raycastResult then endPosition = raycastResult.Position end
        
        if inVR then
            triggerbotResult = raycastResult
        else
            local centerRay = Camera:ViewportPointToRay(Camera.ViewportSize.X * 0.5, Camera.ViewportSize.Y * 0.5)
            triggerbotResult = workspace:Raycast(centerRay.Origin, centerRay.Direction * Options.MaxDistance, mainRaycastParams)
        end
    end

    if triggerbotResult and Options.AutoShoot and (tick() - lastShot >= Options.Cooldown) and not isRobloxMenuOpen then
        local model = triggerbotResult.Instance:FindFirstAncestorOfClass("Model") or triggerbotResult.Instance.Parent
        if model and checkValidTarget(model) then
            lastShot = tick()
            task.spawn(function()
                local screenX = Camera.ViewportSize.X / 2
                local screenY = Camera.ViewportSize.Y / 2
                VirtualInputManager:SendMouseButtonEvent(screenX, screenY, 0, true, game, 0)
                task.wait()
                VirtualInputManager:SendMouseButtonEvent(screenX, screenY, 0, false, game, 0)
            end)
        end
    end
    
    if laserContainer.Transparency < 1 then
        drawLaser(rayOrigin, endPosition)
    end

    local isEspActive = Options.EspHighlight or Options.EspNames or Options.EspHealth or Options.EspDistance or Options.EspTracers or Options.EspTeam or Options.ShowEspIcon or Options.EspHitbox

    local myHrp = character and character:FindFirstChild("HumanoidRootPart")
    local myPos = myHrp and myHrp.Position or Camera.CFrame.Position

    -- ОТРИСОВКА И СКРЫТИЕ ESP (Без дестроев внутри цикла)
    for _, player in ipairs(Players:GetPlayers()) do
        if player == LocalPlayer then continue end

        local pChar = player.Character
        local hrp = pChar and pChar:FindFirstChild("HumanoidRootPart")
        local humanoid = pChar and pChar:FindFirstChildOfClass("Humanoid")
        
        -- Если ESP выключен или игрок недоступен — просто скрываем UI
        if not isEspActive or not pChar or not hrp or not humanoid then
            hideEsp(player)
            continue
        end

        local dist = (myPos - hrp.Position).Magnitude
        if dist > Options.MaxDistance then
            hideEsp(player)
            continue
        end

        local currentHp, maxHp = getHealth(pChar, humanoid)
        if currentHp <= 0 then
            hideEsp(player)
            continue
        end

        -- Гарантируем наличие ESP-объектов
        if not ActiveEspObjects[player] then
            createEsp(player)
        end

        local esp = ActiveEspObjects[player]
        if not esp then continue end

        -- Проверка на команды
        local isAllowedVisual = false
        if Options.EspTeam then
            isAllowedVisual = true
        else
            local isEnemy = true
            if Options.TeamCheck and isAllyFast(player) then isEnemy = false end
            if Options.AntiFriends and FriendsCache[player.Name] then isEnemy = false end
            if Options.Whitelist[player.Name] then isEnemy = false end
            
            if isEnemy then isAllowedVisual = true end
        end

        if not isAllowedVisual then
            hideEsp(player)
            continue
        end

        -- Если проверки пройдены, настраиваем отображение
        if esp.Folder.Parent ~= CoreGui then esp.Folder.Parent = CoreGui end

        local teamColor = player.TeamColor and player.TeamColor.Color or Color3.fromRGB(255, 0, 0)
        local cache = esp.Cache

        -- 1. Chams
        if Options.EspHighlight then
            if esp.Highlight.Adornee ~= pChar then esp.Highlight.Adornee = pChar end
            if esp.Highlight.FillColor ~= teamColor then esp.Highlight.FillColor = teamColor end
            if not esp.Highlight.Enabled then esp.Highlight.Enabled = true end
        else
            if esp.Highlight.Enabled then esp.Highlight.Enabled = false end
        end
		
        -- 2. Hitbox Box
        if Options.EspHitbox and Options.HitboxSilentAim then
            local currentHitboxSize = Options.HitboxSize or 10
            local targetSize = Vector3.new(currentHitboxSize, currentHitboxSize, currentHitboxSize)

            if esp.BoxAdornment.Adornee ~= hrp then 
                esp.BoxAdornment.Adornee = hrp 
            end
            if esp.BoxAdornment.Size ~= targetSize then
                esp.BoxAdornment.Size = targetSize
            end
            if esp.BoxAdornment.Color3 ~= teamColor then 
                esp.BoxAdornment.Color3 = teamColor
            end
            if esp.BoxAdornment.Transparency ~= Options.EspHitboxTransparency then
                esp.BoxAdornment.Transparency = Options.EspHitboxTransparency
            end
            if not esp.BoxAdornment.Visible then 
                esp.BoxAdornment.Visible = true 
            end

            if esp.SelectionBox.Adornee ~= hrp then 
                esp.SelectionBox.Adornee = hrp
            end
            if esp.SelectionBox.Color3 ~= teamColor then 
                esp.SelectionBox.Color3 = teamColor
            end
        else
            if esp.BoxAdornment.Visible then 
                esp.BoxAdornment.Visible = false 
            end
            if esp.BoxAdornment.Adornee ~= nil then 
                esp.BoxAdornment.Adornee = nil 
            end
            if esp.SelectionBox.Adornee ~= nil then 
                esp.SelectionBox.Adornee = nil 
            end
        end

        -- 3. Billboard Text / Icons
        local showText = Options.EspNames or Options.EspHealth or Options.EspDistance
        local showIcon = Options.ShowEspIcon

        if showText or showIcon then
            if esp.Billboard.Adornee ~= hrp then esp.Billboard.Adornee = hrp end
            if not esp.Billboard.Enabled then esp.Billboard.Enabled = true end

            local iconSize = 40

            local finalIconSize = UDim2.new(0, iconSize, 0, iconSize)
            if esp.IconImage.Size ~= finalIconSize then
                esp.IconImage.Size = finalIconSize
            end
            
            local labelPos = UDim2.new(0.5, 0, 0, iconSize + 5)
            if esp.Label.Position ~= labelPos then
                esp.Label.Position = labelPos
            end
            
            local textSize = 12
            if esp.Label.TextSize ~= textSize then
                esp.Label.TextSize = textSize
            end

            if showText then
                if not esp.Label.Visible then esp.Label.Visible = true end
                
                local hpInt = math.floor(currentHp)
                local maxHpInt = math.floor(maxHp)
                local distInt = math.floor(dist)
                
                if cache.Health ~= hpInt or cache.Dist ~= distInt then
                    cache.Health = hpInt
                    cache.Dist = distInt
                    
                    local labelText = ""
                    if Options.EspNames then labelText = labelText .. player.Name .. "\n" end
                    if Options.EspHealth then labelText = labelText .. "HP: " .. hpInt .. "/" .. maxHpInt .. " " end
                    if Options.EspDistance then labelText = labelText .. "[" .. distInt .. "m]" end
                    
                    if esp.Label.Text ~= labelText then
                        esp.Label.Text = labelText
                    end
                end
            else
                if esp.Label.Visible then esp.Label.Visible = false end
            end
            
            if showIcon then
                if not esp.IconImage.Visible then esp.IconImage.Visible = true end
            else
                if esp.IconImage.Visible then esp.IconImage.Visible = false end
            end
        else
            if esp.Billboard.Enabled then esp.Billboard.Enabled = false end
        end

        -- 4. Tracers
        local tracer = ActiveTracers[player]
        if Options.EspTracers and tracer then
            local screenPos, onScreen = Camera:WorldToViewportPoint(hrp.Position)
            if onScreen then
                if tracer.Color ~= teamColor then tracer.Color = teamColor end
                local fromVec = Vector2.new(Camera.ViewportSize.X * 0.5, Camera.ViewportSize.Y)
                if tracer.From ~= fromVec then tracer.From = fromVec end
                local toVec = Vector2.new(screenPos.X, screenPos.Y)
                if tracer.To ~= toVec then tracer.To = toVec end
                if not tracer.Visible then tracer.Visible = true end
            else
                if tracer.Visible then tracer.Visible = false end
            end
        elseif tracer then
            if tracer.Visible then tracer.Visible = false end
        end
    end
end

RunService:BindToRenderStep(renderStepName, Enum.RenderPriority.Camera.Value, onRenderStep)

Rayfield:LoadConfiguration()
WhitelistDropdown:Set({""})
