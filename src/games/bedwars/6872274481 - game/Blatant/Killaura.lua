local Attacking
run(function()
    local Killaura
    local Targets
    local Sort
    local SwingRange
    local AttackRange
    local RangeCircle
    local RangeCirclePart
    local UpdateRate
    local AngleSlider
    local MaxTargets
    local Mouse
    local Swing
    local GUI
    local BoxSwingColor
    local BoxAttackColor
    local ParticleTexture
    local ParticleColor1
    local ParticleColor2
    local ParticleSize
    local Face
    local FaceSpeed
    local Animation
    local AnimationMode
    local AnimationSpeed
    local AnimationTween
    local Limit
    local LegitAura
    local SyncHits
    local lastAttackTime = 0
    local lastManualSwing = 0
    local lastSwingServerTime = 0
    local lastSwingServerTimeDelta = 0
    local AttackCheck
    local kitChecks
    local SwingTime
    local SwingTimeSlider
    local swingCooldown = 0
    local ContinueSwinging
    local ContinueSwingTime
    local lastTargetTime = 0
    local continueSwingCount = 0
    local Particles, Boxes = {}, {}
    local anims, AnimDelay, AnimTween, armC0 = vape.Libraries.auraanims, tick()
    local AttackRemote
    local TargetPriority
    local CustomHitReg
    local CustomHitRegSlider
    local lastCustomHitTime = 0
    local AirHit
    local AirHitsChance
    local FROZEN_THRESHOLD = 10
    local FastHits
    local FastHitsMode
    local LegitSwitch
    local OldShootInterval
    local OldSwitchDelay
    local OldWaitDelay
    local OldFirstPersonCheck
    local lastOldShootTime = 0
    local Legit
    local FireRate
    local autoShootLoop = nil
    local projectileRemote = {InvokeServer = function() end}
    local ProjectileDelay = {}
    local FastHitsFireDelays = {}
    local fhUsageIndex = 1
    local responded = true
    local preserveSwordIcon = false
    local FASTHITS_HIT_DEBOUNCE = 0.1
    local fastHitsHitTarget = nil
    local fastHitsTrackedEntity = nil
    local fastHitsHitCount = 0
    local fastHitsActivationReady = false
    local fastHitsLastHitTime = 0

    task.spawn(function()
        AttackRemote = bedwars.Client:Get(remotes.AttackEntity).instance
        projectileRemote = bedwars.Client:Get(remotes.FireProjectile).instance
    end)

    local DynamicReach
    local lastOptimizedAttackTime = 0

    local function optimizeHitData(selfpos, targetpos, delta, cameraPosition, cursorDirection)
        if not DynamicReach or not DynamicReach.Enabled then return true end
        if not selfpos or not targetpos or not delta or not cameraPosition or not cursorDirection then return true end
        local direction = (targetpos - selfpos).Unit
        local selfPush, targetPull
        if delta > 20 then selfPush, targetPull = 2.6, 0.95
        elseif delta > 18 then selfPush, targetPull = 2.4, 0.7
        elseif delta > 14.4 then selfPush, targetPull = 2.2, 0.5
        elseif delta > 10 then selfPush, targetPull = 1.8, 0.3
        else selfPush, targetPull = 0.6, 0 end
        local optimizedSelfPos = selfpos + (direction * selfPush) + Vector3.new(0, 0.8, 0)
        local optimizedTargetPos = targetpos - (direction * targetPull) + Vector3.new(0, 1.2, 0)
        local camToTarget = (targetpos - cameraPosition).Unit
        local camPush
        if delta > 20 then camPush = 2.2
        elseif delta > 18 then camPush = 1.8
        elseif delta > 14.4 then camPush = 1.4
        elseif delta > 10 then camPush = 0.9
        else camPush = 0.4 end
        local optimizedCameraPos = cameraPosition + (camToTarget * camPush) + Vector3.new(0, 0.4, 0)
        local optimizedCamToTarget = (optimizedTargetPos - optimizedCameraPos).Unit
        local blendFactor
        if delta > 20 then blendFactor = 0.945
        elseif delta > 18 then blendFactor = 0.75
        elseif delta > 14.4 then blendFactor = 0.55
        elseif delta > 10 then blendFactor = 0.35
        else blendFactor = 0.15 end
        local optimizedCursorDirection = (cursorDirection + (optimizedCamToTarget * blendFactor)).Unit
        return optimizedSelfPos, optimizedTargetPos, optimizedCameraPos, optimizedCursorDirection
    end

    local function getOptimizedAttackTiming(delta)
        if not DynamicReach or not DynamicReach.Enabled then return true end
        if not delta then return false end
        local currentTime = tick()
        local delayBetweenAttacks
        if delta > 20 then delayBetweenAttacks = 0.38
        elseif delta > 18 then delayBetweenAttacks = 0.18
        elseif delta > 14.4 then delayBetweenAttacks = 0.09
        elseif delta > 10 then delayBetweenAttacks = 0.04
        else delayBetweenAttacks = 0 end
        local elapsed = currentTime - lastOptimizedAttackTime
        if elapsed >= delayBetweenAttacks then
            lastOptimizedAttackTime = elapsed > delayBetweenAttacks * 2 and currentTime or lastOptimizedAttackTime + delayBetweenAttacks
            return true
        end
        return false
    end

    local function canHitWithCustomReg()
        if not CustomHitReg or not CustomHitReg.Enabled then return true end
        if not CustomHitRegSlider then return true end
        if CustomHitRegSlider.Value >= 36 then return true end
        local currentTime = tick()
        local delayBetweenHits = 10 / CustomHitRegSlider.Value
        if currentTime - lastCustomHitTime >= delayBetweenHits then
            lastCustomHitTime = lastCustomHitTime + delayBetweenHits
            if currentTime - lastCustomHitTime > delayBetweenHits then
                lastCustomHitTime = currentTime
            end
            return true
        end
        return false
    end

    local _t4LastHit = {}

    local function FireAttackRemote(attackTable)
        if not AttackRemote then return end
        if not canHitWithCustomReg() then return end
        local _atkPlr = playersService:GetPlayerFromCharacter(attackTable.entityInstance)
        if _atkPlr then
            local targetTier = getAccountTier(_atkPlr)
            if targetTier >= 99 then return end
            if targetTier == 4 and getAccountTier(lplr) <= 2 then
                local uid = _atkPlr.UserId
                local now = tick()
                if _t4LastHit[uid] and now - _t4LastHit[uid] < (10/32) then return end
                _t4LastHit[uid] = now
            end
            -- whitelist removed
        end
        if DynamicReach and DynamicReach.Enabled then
            if not getOptimizedAttackTiming((attackTable.validate.selfPosition.value - attackTable.validate.targetPosition.value).Magnitude) then
                return
            end
            local ns, nt, nc, ncu = optimizeHitData(
                attackTable.validate.selfPosition.value,
                attackTable.validate.targetPosition.value,
                (attackTable.validate.selfPosition.value - attackTable.validate.targetPosition.value).Magnitude,
                attackTable.validate.raycast.cameraPosition.value,
                attackTable.validate.raycast.cursorDirection.value
            )
            if ns then
                attackTable.validate.selfPosition.value = ns
                attackTable.validate.targetPosition.value = nt
                attackTable.validate.raycast.cameraPosition.value = nc
                attackTable.validate.raycast.cursorDirection.value = ncu
            end
        end
        return AttackRemote:FireServer(attackTable)
    end

    local function createRangeCircle()
        local suc, err = pcall(function()
            if (not shared.CheatEngineMode) then
                RangeCirclePart = Instance.new("MeshPart")
                RangeCirclePart.MeshId = "rbxassetid://3726303797"
                if shared.RiseMode and GuiLibrary.GUICoreColor and GuiLibrary.GUICoreColorChanged then
                    RangeCirclePart.Color = GuiLibrary.GUICoreColor
                    GuiLibrary.GUICoreColorChanged.Event:Connect(function()
                        RangeCirclePart.Color = GuiLibrary.GUICoreColor
                    end)
                else
                    RangeCirclePart.Color = Color3.fromHSV(BoxSwingColor["Hue"], BoxSwingColor["Sat"], BoxSwingColor.Value)
                end
                RangeCirclePart.CanCollide = false
                RangeCirclePart.Anchored = true
                RangeCirclePart.Material = Enum.Material.Neon
                RangeCirclePart.Size = Vector3.new(SwingRange.Value * 0.7, 0.01, SwingRange.Value * 0.7)
                if Killaura.Enabled then
                    RangeCirclePart.Parent = gameCamera
                end
                RangeCirclePart:SetAttribute("gamecore_GameQueryIgnore", true)
            end
        end)
        if (not suc) then
            pcall(function()
                if RangeCirclePart then
                    RangeCirclePart:Destroy()
                    RangeCirclePart = nil
                end
                notif("Killaura - Range Visualiser Circle", "There was an error creating the circle. Disabling...", 2)
            end)
        end
    end

    local function getAttackData()
        if AttackCheck and AttackCheck.Enabled then
            local stunTime = lplr.Character and lplr.Character:GetAttribute('StunnedUntilTime')
            if stunTime and stunTime > workspace:GetServerTimeNow() then return false end
            if kitChecks then
                for _, check in pairs(kitChecks) do
                    if check() then return false end
                end
            end
        end

        if Mouse and Mouse.Enabled then
            local recentSwing = LegitAura and LegitAura.Enabled and (tick() - bedwars.SwordController.lastSwing) <= 0.2
            if not recentSwing then
                local mousePressed = inputService:IsMouseButtonPressed(Enum.UserInputType.MouseButton1)
                if not mousePressed then return false end
            end
        end

        if tick() - store.silasAbilityTime < 2.2 then return false end
        if tick() - store.terraStompTime < 0.7 then return false end
        if tick() - store.terraKickTime < 0.5 then return false end

        if GUI and GUI.Enabled then
            if bedwars.AppController:isLayerOpen(bedwars.UILayers.MAIN) then return false end
        end

        local sword = Limit and Limit.Enabled and store.hand or store.tools.sword
        if not sword or not sword.tool then return false end

        local meta = bedwars.ItemMeta[sword.tool.Name]
        if not meta then return false end

        if Limit and Limit.Enabled then
            if store.hand.toolType ~= 'sword' or bedwars.DaoController.chargingMaid then return false end
        end

        if LegitAura and LegitAura.Enabled then
            if (tick() - bedwars.SwordController.lastSwing) > 0.2 then return false end
        end

        if SwingTime and SwingTime.Enabled then
            local swingSpeed = SwingTimeSlider.Value
            if (tick() - lastAttackTime) < swingSpeed then return false end
        end
        return sword, meta
    end

    local function resetSwordCooldown()
        if bedwars.SwordController then
            bedwars.SwordController.lastAttack = 0
            bedwars.SwordController.lastSwing = 0
            if bedwars.SwordController.lastChargedAttackTimeMap then
                for weaponName, _ in pairs(bedwars.SwordController.lastChargedAttackTimeMap) do
                    bedwars.SwordController.lastChargedAttackTimeMap[weaponName] = 0
                end
            end
        end
    end

    local function shouldContinueSwinging()
        if not ContinueSwinging or not ContinueSwinging.Enabled then return false end
        if lastTargetTime == 0 then return false end
        return (tick() - lastTargetTime) <= ContinueSwingTime.Value
    end

    local function getAmmo(check)
        for _, item in store.inventory.inventory.items do
            if check.ammoItemTypes and table.find(check.ammoItemTypes, item.itemType) then
                return item.itemType
            end
        end
    end

    local _projectilesCache = {}
    local _projectilesCacheTime = 0
    local function getProjectiles()
        local now = tick()
        if now - _projectilesCacheTime < 0.5 and #_projectilesCache > 0 then
            return _projectilesCache
        end
        _projectilesCacheTime = now
        table.clear(_projectilesCache)
        for _, item in store.inventory.inventory.items do
            local meta = bedwars.ItemMeta[item.itemType]
            if not meta then continue end
            local proj = meta.projectileSource
            local ammo = proj and getAmmo(proj)
            if ammo and table.find({'arrow'}, ammo) then
                table.insert(_projectilesCache, {
                    item,
                    ammo,
                    proj.projectileType(ammo),
                    proj
                })
            end
        end
        return _projectilesCache
    end

    local function canShoot(proj)
        return tick() > (ProjectileDelay[proj[1].itemType] or 0)
    end

    local sharedFastHitsRayParams = RaycastParams.new()
    local function shootProjectile(item, ammo, projectile, itemMeta, selfPos, ent, ignoreSwitch)
        local meta = bedwars.ProjectileMeta[projectile]
        if not meta then return false end

        local projSpeed = meta.launchVelocity
        local gravity = meta.gravitationalAcceleration or 196.2
        local targetPart = ent.RootPart
        local targetVel = targetPart.Velocity
        local playerGravity = workspace.Gravity
        local balloons = ent.Character and ent.Character:GetAttribute('InflatedBalloons')
        if balloons and balloons > 0 then
            playerGravity = workspace.Gravity * (1 - (balloons >= 4 and 1.2 or balloons >= 3 and 1 or 0.975))
        end
        if ent.Character and ent.Character.PrimaryPart and ent.Character.PrimaryPart:FindFirstChild('rbxassetid://8200754399') then
            playerGravity = 6
        end
        if ent.Player and ent.Player:GetAttribute('IsOwlTarget') then
            local _owls = collectionService:GetTagged('Owl')
            if #_owls > 0 then
                local _uid = ent.Player.UserId
                for _, owl in ipairs(_owls) do
                    if owl:GetAttribute('Target') == _uid and owl:GetAttribute('Status') == 2 then
                        playerGravity = 0
                        break
                    end
                end
            end
        end

        local bowRelX = bedwars.BowConstantsTable.RelX or 0
        local bowRelY = bedwars.BowConstantsTable.RelY or 0
        local bowRelZ = bedwars.BowConstantsTable.RelZ or 0
        local ping = math.clamp(lplr:GetNetworkPing(), 0.03, 0.25) 
        local chestPos = targetPart.Position + Vector3.new(0, (ent.HipHeight or 2) * (ammo == 'fireball' and 1.0 or 0.15), 0)
        local extPos = chestPos + targetVel * ping
        local lookCF = CFrame.new(selfPos, extPos) * CFrame.new(bowRelX, bowRelY, bowRelZ)

        local calc = prediction.SolveTrajectory(
            lookCF.p,
            projSpeed,
            gravity,
            extPos,
            targetVel,
            playerGravity,
            ent.HipHeight or 2,
            ent.Jumping and 42.6 or nil,
            sharedFastHitsRayParams
        )

        if not calc then return false end

        local switched = false
        if not ignoreSwitch then
            switched = switchItem(item.tool, 0.05)
        end

        local aimCF = CFrame.lookAt(lookCF.Position, calc)
        local dir = aimCF.LookVector
        local shootPos = (aimCF * CFrame.new(-bowRelX, -bowRelY, -bowRelZ)).Position
        local id = httpService:GenerateGUID(true)

        targetinfo.Targets[ent] = tick() + 1
        ProjectileDelay[item.itemType] = tick() + (itemMeta.fireDelaySec or 0.5)
        bedwars.ProjectileController:createLocalProjectile(
            meta, ammo, projectile, shootPos, id, dir * projSpeed,
            {drawDurationSeconds = 1}
        )

		task.spawn(function()
		local res = projectileRemote:InvokeServer(
			item.tool, ammo, projectile, shootPos, selfPos,
			dir * projSpeed, id,
			{drawDurationSeconds = 1, shotId = httpService:GenerateGUID(false)},
			workspace:GetServerTimeNow() - ping
		)
		if res then
			pcall(function() res.Parent = replicatedStorage end)
			local sound = itemMeta.launchSound
			sound = sound and sound[math.random(1, #sound)] or nil
			if sound then bedwars.SoundManager:playSound(sound) end
		else
			ProjectileDelay[item.itemType] = tick() + (itemMeta.fireDelaySec or 0.5) + 0.1
		end
	end)

        if switched and not ignoreSwitch then task.wait(0.05) end
        return true
    end

    local function doFastHitsNEW(ent)
        if not ent or not ent.RootPart then return end
        if not entitylib.isAlive then return end

        local selfPos = entitylib.character.RootPart.Position
        local projectiles = getProjectiles()
        if not projectiles or #projectiles == 0 then return end
        local startIndex = fhUsageIndex
        local found = false
        repeat
            fhUsageIndex = fhUsageIndex % #projectiles + 1
            if canShoot(projectiles[fhUsageIndex]) then
                found = true
                break
            end
        until fhUsageIndex == startIndex

        if not found then return end

        local item, ammo, projectile, itemMeta = unpack(projectiles[fhUsageIndex])
        shootProjectile(item, ammo, projectile, itemMeta, selfPos, ent, false)
    end

    local function doFastHitsLegitSwitch(ent)
        if not ent or not ent.RootPart then return end
        if not entitylib.isAlive then return end

        local selfPos = entitylib.character.RootPart.Position
        local projectiles = getProjectiles()
        if not projectiles or #projectiles == 0 then return end
		
        local readyProj = nil
        for _, proj in projectiles do
            if canShoot(proj) then
                readyProj = proj
                break
            end
        end

        if not readyProj then return end
        local item, ammo, projectile, itemMeta = unpack(readyProj)
        local bowSlot = nil
        local swordSlot = nil
        local originalSlot = store.inventory.hotbarSlot
        local hotbar = store.inventory.hotbar
        for i = 1, #hotbar do
            local hv = hotbar[i]
            if hv and hv.item and hv.item.itemType then
                if hv.item.itemType == item.itemType and not bowSlot then
                    bowSlot = i - 1
                end
                local hm = bedwars.ItemMeta[hv.item.itemType]
                if hm and hm.sword and not swordSlot then
                    swordSlot = i - 1
                end
            end
        end

        if not bowSlot then return end
        if hotbarSwitch(bowSlot) then task.wait(0.05) end

        local isCrossbow = item.itemType:find('crossbow')
        if isCrossbow then
            pcall(function() bedwars.ViewmodelController:playAnimation(bedwars.AnimationType.FP_CROSSBOW_FIRE) end)
            bedwars.GameAnimationUtil:playAnimation(lplr, bedwars.AnimationType.CROSSBOW_FIRE)
        else
            pcall(function() bedwars.ViewmodelController:playAnimation(bedwars.AnimationType.FP_CROSSBOW_FIRE) end)
            bedwars.GameAnimationUtil:playAnimation(lplr, bedwars.AnimationType.BOW_FIRE)
        end

        shootProjectile(item, ammo, projectile, itemMeta, selfPos, ent, true)

        task.wait(0.05)
        hotbarSwitch(swordSlot or originalSlot)
    end

    local function doOldFastHits()
        if not store.KillauraTarget then return end
        local currentTime = tick()
        if (currentTime - lastOldShootTime) < OldShootInterval.Value then return end

        if OldFirstPersonCheck and OldFirstPersonCheck.Enabled then
            local cf = gameCamera.CFrame
            local char = entitylib.character
            if char and char.RootPart then
                local dist = (cf.Position - char.RootPart.Position).Magnitude
                if dist > 1 then return end
            end
        end

        local arrowItem = getItem('arrow')
        if not arrowItem or arrowItem.amount <= 0 then return end

        local bows = {}
        local swordSlot = nil
        local hotbar = store.inventory.hotbar
        for i = 1, #hotbar do
            local v = hotbar[i]
            if v and v.item and v.item.itemType then
                local itemMeta = bedwars.ItemMeta[v.item.itemType]
                if itemMeta then
                    if itemMeta.projectileSource then
                        local ps = itemMeta.projectileSource
                        if ps.ammoItemTypes and table.find(ps.ammoItemTypes, 'arrow') then
                            table.insert(bows, i - 1)
                        end
                    end
                    if itemMeta.sword and not swordSlot then
                        swordSlot = i - 1
                    end
                end
            end
        end

        if #bows == 0 then return end

        lastOldShootTime = currentTime
        local originalSlot = store.inventory.hotbarSlot
        for i = 1, #bows do
            local bowSlot = bows[i]
            if hotbarSwitch(bowSlot) then
                task.wait(OldSwitchDelay.Value)
                leftClick()
                task.wait(0.05)
            end
        end
        if swordSlot then
            hotbarSwitch(swordSlot)
        else
            hotbarSwitch(originalSlot)
        end
    end

    local function getEntityFromCharacterFH(char)
        for _, ent in ipairs(entitylib.List) do
            if ent.Character == char then return ent end
        end
        return nil
    end

    local function doFastHits()
        if not FastHits or not FastHits.Enabled then return end
        if not Killaura or not Killaura.Enabled then return end
        if not Attacking then return end
        if not store.KillauraTarget then return end
        if not entitylib.isAlive then return end

        local ent = store.KillauraTarget
        if not ent or not ent.RootPart then return end
        local selfPos = entitylib.character.RootPart.Position
        local dist = (ent.RootPart.Position - selfPos).Magnitude
        if dist > (AttackRange.Value + 2) then return end

        if FireRate and FireRate.Value > 0 then
            local now = tick()
            if (now - (ProjectileDelay._lastFHShot or 0)) < FireRate.Value then return end
            ProjectileDelay._lastFHShot = now
        end

        local mode = FastHitsMode and FastHitsMode.Value or 'NEWFastHits'
        if mode == 'NEWFastHits' then
            if LegitSwitch and LegitSwitch.Enabled then
                doFastHitsLegitSwitch(ent)
            else
                doFastHitsNEW(ent)
            end
        elseif mode == 'OLDFastHits' then
            doOldFastHits()
        end
    end

    local function startAutoShootLoop()
        if autoShootLoop then return end
        fastHitsHitTarget = nil
        fastHitsTrackedEntity = nil
        fastHitsHitCount = 0
        fastHitsActivationReady = false
        fastHitsLastHitTime = 0
        fhUsageIndex = 1
        table.clear(ProjectileDelay)
        table.clear(FastHitsFireDelays)

        autoShootLoop = task.spawn(function()
            while Killaura and Killaura.Enabled and FastHits and FastHits.Enabled do
                doFastHits()
                task.wait(0.05)
            end
            autoShootLoop = nil
        end)
    end

    local function stopAutoShootLoop()
        if autoShootLoop then
            task.cancel(autoShootLoop)
            autoShootLoop = nil
        end
        table.clear(ProjectileDelay)
        table.clear(FastHitsFireDelays)
        fhUsageIndex = 1
        fastHitsHitTarget = nil
        fastHitsTrackedEntity = nil
        fastHitsHitCount = 0
        fastHitsActivationReady = false
        fastHitsLastHitTime = 0
    end

    local attacked = {}
    local hadTargetsLastTick = false
    Killaura = vape.Categories.Blatant:CreateModule({
        Name = 'Killaura',
        Function = function(callback)
            if callback then
                lastAttackTime = 0
                swingCooldown = 0
                lastTargetTime = 0
                continueSwingCount = 0
                resetSwordCooldown()
                if Mouse and LegitAura and Mouse.Enabled and LegitAura.Enabled then
                    Mouse:Toggle(false)
                    LegitAura:Toggle(false)
                    notif("Killaura", "yo u cant have require mouse down AND swing only both on at da same time turned both off 4 u", 5)
                end

                if RangeCircle and RangeCircle.Enabled then
                    createRangeCircle()
                end
                if inputService.TouchEnabled and not preserveSwordIcon then
                    pcall(function()
                        lplr.PlayerGui.MobileUI['2'].Visible = Limit and Limit.Enabled
                    end)
                end

                 if FastHits and FastHits.Enabled then
                    startAutoShootLoop()
                end

                if Animation and Animation.Enabled and not (identifyexecutor and table.find({'Argon', 'Delta'}, ({identifyexecutor()})[1])) then
                    task.spawn(function()
                        local started = false
                        repeat
                            if Attacking then
                                if not armC0 then
                                    armC0 = gameCamera.Viewmodel.RightHand.RightWrist.C0
                                end
                                local first = not started
                                started = true
                                if AnimationMode.Value == 'Random' then
                                    anims.Random = {{CFrame = CFrame.Angles(math.rad(math.random(1, 360)), math.rad(math.random(1, 360)), math.rad(math.random(1, 360))), Time = 0.12}}
                                end
                                for _, v in anims[AnimationMode.Value] do
                                    if AnimTween then AnimTween:Destroy() AnimTween = nil end
                                	AnimTween = tweenService:Create(gameCamera.Viewmodel.RightHand.RightWrist, TweenInfo.new(first and (AnimationTween.Enabled and 0.001 or 0.1) or v.Time / AnimationSpeed.Value, Enum.EasingStyle.Linear), {
                                        C0 = armC0 * v.CFrame
                                    })
                                    AnimTween:Play()
                                    AnimTween.Completed:Wait()
                                    first = false
                                    if (not Killaura.Enabled) or (not Attacking) then break end
                                end
                            elseif started then
                                started = false
                                if AnimTween then AnimTween:Destroy() AnimTween = nil end
                                AnimTween = tweenService:Create(gameCamera.Viewmodel.RightHand.RightWrist, TweenInfo.new(AnimationTween.Enabled and 0.001 or 0.3, Enum.EasingStyle.Exponential), {
                                    C0 = armC0
                                })
                                AnimTween:Play()
                            end
                            if not started then
                                task.wait(1 / UpdateRate.Value)
                            end
                        until (not Killaura.Enabled) or (not Animation.Enabled)
                    end)
                end

                local function gatherTargets(selfpos)
                        local walls = Targets.Walls.Enabled or nil
                        local players = Targets.Players.Enabled
                        local npcs = Targets.NPCs.Enabled
                        local limit = MaxTargets.Value
                        local sort = sortmethods[Sort.Value]
                        local swingPlrs = entitylib.AllPosition({
                            Range = SwingRange.Value,
                            Wallcheck = walls,
                            Part = 'RootPart',
                            Players = players,
                            NPCs = npcs,
                            Limit = limit,
                            Sort = sort
                        })
                        if AttackRange.Value == SwingRange.Value then
                            return swingPlrs, swingPlrs
                        end
                        local attackPlrs = entitylib.AllPosition({
                            Range = AttackRange.Value,
                            Wallcheck = walls,
                            Part = 'RootPart',
                            Players = players,
                            NPCs = npcs,
                            Limit = limit,
                            Sort = sort
                        })
                        return swingPlrs, attackPlrs
                    end

                local _cachedSwordType = nil
                local _cachedIsClaw = false
                local _swingCooldown = 0

                repeat
                    if AttackCheck and AttackCheck.Enabled then
                        local triggered = false
                        local stunTime = lplr.Character and lplr.Character:GetAttribute('StunnedUntilTime')
                        if stunTime and stunTime > workspace:GetServerTimeNow() then triggered = true end
                        if not triggered and kitChecks then
                            for _, check in pairs(kitChecks) do
                                if check() then triggered = true break end
                            end
                        end
                        if triggered then
                            Attacking = false
                            store.KillauraTarget = nil
                            task.wait(0.3)
                            continue
                        end
                    end

                    pcall(function()
                        if entitylib.isAlive and entitylib.character.HumanoidRootPart and RangeCirclePart then
                            RangeCirclePart.Position = entitylib.character.HumanoidRootPart.Position - Vector3.new(0, entitylib.character.Humanoid.HipHeight, 0)
                        end
                    end)

                    table.clear(attacked)
                    local sword, meta = getAttackData()
                    Attacking = false
                    store.KillauraTarget = nil

                    if vapeTargetInfo and vapeTargetInfo.Targets then
                        vapeTargetInfo.Targets.Killaura = nil
                    end

                    if sword then
                        if sword.itemType ~= _cachedSwordType then
                            _cachedSwordType = sword.itemType
                            _cachedIsClaw = sword.itemType and sword.itemType:find("summoner_claw") ~= nil
                        end
                        local isClaw = _cachedIsClaw

                        local selfpos = entitylib.character.RootPart.Position
                        local flatLV = entitylib.character.RootPart.CFrame.LookVector * Vector3.new(1, 0, 1)
                        local localfacing = flatLV.Magnitude > 0.001 and flatLV.Unit or entitylib.character.RootPart.CFrame.RightVector
                        local maxAngle = math.rad(AngleSlider.Value) / 2
                        local _cachedPing = math.clamp(lplr:GetNetworkPing(), 0.03, 0.4)
                        local swingPlrs, attackPlrs = gatherTargets(selfpos)

                        local hasValidSwingTargets = false
                        local hasValidAttackTargets = false

						for _, v in swingPlrs do
							local flat = (v.RootPart.Position - selfpos) * Vector3.new(1, 0, 1)
							if flat.Magnitude <= 1.0 or math.acos(math.clamp(localfacing:Dot(flat.Unit), -1, 1)) <= maxAngle then
								hasValidSwingTargets = true
								break
							end
						end

						for _, v in attackPlrs do
							local flat = (v.RootPart.Position - selfpos) * Vector3.new(1, 0, 1)
							if flat.Magnitude <= 1.0 or math.acos(math.clamp(localfacing:Dot(flat.Unit), -1, 1)) <= maxAngle then
								hasValidAttackTargets = true
								break
							end
						end

                        if hasValidSwingTargets or hasValidAttackTargets then
                            lastTargetTime = tick()
                        end

                        if hasValidAttackTargets and not hadTargetsLastTick then
                            resetSwordCooldown()
                        end
                        hadTargetsLastTick = hasValidAttackTargets

                        local shouldSwing = hasValidSwingTargets or hasValidAttackTargets or shouldContinueSwinging()

                        if shouldSwing then
                            switchItem(sword.tool, 0)

                            if hasValidAttackTargets then
                                for _, v in attackPlrs do
                                    local delta = v.RootPart.Position - selfpos
                                    local flat = delta * Vector3.new(1, 0, 1)
                                    if flat.Magnitude > 1.0 and math.acos(math.clamp(localfacing:Dot(flat.Unit), -1, 1)) > maxAngle then continue end

                                    table.insert(attacked, {
                                        Entity = v,
                                        Check = delta.Magnitude > AttackRange.Value and BoxSwingColor or BoxAttackColor
                                    })
                                    targetinfo.Targets[v] = tick() + 1

                                    if vapeTargetInfo and vapeTargetInfo.Targets then
                                        local info = {Humanoid = {Health = v.Health, MaxHealth = v.MaxHealth}, Player = v.Player}
                                        vapeTargetInfo.Targets.Killaura = info
                                    end

                                    if not Attacking then
                                        Attacking = true
                                        store.KillauraTarget = v
                                        if not isClaw then
                                            local allowSwingAnim = not (Swing and Swing.Enabled) and AnimDelay <= tick() and not (LegitAura and LegitAura.Enabled)
                                            if allowSwingAnim then
                                                local swingSpeed = SwingTime and SwingTime.Enabled and math.max(SwingTimeSlider.Value, 0.11) or (meta.sword and meta.sword.respectAttackSpeedForEffects and meta.sword.attackSpeed or 0.25)
                                                AnimDelay = tick() + swingSpeed
                                                pcall(function()
                                                    bedwars.SwordController:playSwordEffect(meta, false)
                                                    if meta.displayName:find(' Scythe') then
                                                        bedwars.ScytheController:playLocalAnimation()
                                                    end
                                                end)
                                                if vape.ThreadFix and setthreadidentity then
                                                    pcall(setthreadidentity, 8)
                                                end
                                            end
                                        end
                                    end

                                    local predictedPos = v.RootPart.Position + v.RootPart.Velocity * _cachedPing
                                    local canHit = (predictedPos - selfpos).Magnitude <= AttackRange.Value
                                    if not canHit then continue end

                                    if AirHit and AirHit.Enabled then
                                        local humanoid = v.Character:FindFirstChildOfClass("Humanoid")
                                        if humanoid then
                                            local state = humanoid:GetState()
                                            if state == Enum.HumanoidStateType.Jumping or state == Enum.HumanoidStateType.Freefall or state == Enum.HumanoidStateType.Physics then
                                                if math.random(1, 100) > AirHitsChance.Value then continue end
                                            end
                                        end
                                    end

                                    local swingSpeed = SwingTime and SwingTime.Enabled and SwingTimeSlider.Value or (meta.sword and meta.sword.respectAttackSpeedForEffects and meta.sword.attackSpeed or 0.42)
                                    if SyncHits and SyncHits.Enabled then
                                        local timeSinceLastSwing = tick() - swingCooldown
                                        if timeSinceLastSwing < math.max(swingSpeed * 0.15, 0.03) then continue end
                                    end

                                    local actualRoot = v.Character.PrimaryPart
                                    if not actualRoot then continue end

                                    local targetPos = actualRoot.Position + actualRoot.Velocity * _cachedPing
                                    local camOrigin = gameCamera.CFrame.Position
                                    local dir = CFrame.lookAt(camOrigin, targetPos).LookVector
                                    local spoofedPos = camOrigin + dir * math.max((targetPos - camOrigin).Magnitude - 14.399, 0)

                                    if SyncHits and SyncHits.Enabled then
                                        if (tick() - swingCooldown) >= math.max(swingSpeed * 0.15, 0.03) then
                                            swingCooldown = tick()
                                        end
                                    else
                                        swingCooldown = tick()
                                    end

                                    local _serverNow = workspace:GetServerTimeNow()
                                    lastSwingServerTimeDelta = _serverNow - lastSwingServerTime
                                    lastSwingServerTime = _serverNow
                                    store.attackReach = (delta.Magnitude * 100) // 1 / 100
                                    store.attackReachUpdate = tick() + 1
                                    lastAttackTime = tick()

                                    if delta.Magnitude < 14.4 and SwingTime and SwingTime.Enabled and SwingTimeSlider.Value > 0.11 then
                                        AnimDelay = tick()
                                    end

                                    if isClaw then
                                        pcall(function() KaidaController:request(v.Character) end)
                                    else
                                        bedwars.SwordController.lastAttack = _serverNow
                                        _swingCooldown = tick()
                                        FireAttackRemote({
                                            weapon = sword.tool,
                                            chargedAttack = {chargeRatio = 0},
                                            lastSwingServerTimeDelta = math.clamp(lastSwingServerTimeDelta, 0.2, 0.8),
                                            entityInstance = v.Character,
                                            validate = {
                                                raycast = {
                                                    cameraPosition = {value = camOrigin},
                                                    cursorDirection = {value = dir}
                                                },
                                                targetPosition = {value = targetPos},
                                                selfPosition = {value = spoofedPos}
                                            }
                                        })
                                    end
                                end
                            else
                                Attacking = true
                                if not isClaw then
                                    if not (Swing and Swing.Enabled) and AnimDelay <= tick() and not (LegitAura and LegitAura.Enabled) then
                                        local swingSpeed = SwingTime and SwingTime.Enabled and math.max(SwingTimeSlider.Value, 0.11) or (meta.sword and meta.sword.respectAttackSpeedForEffects and meta.sword.attackSpeed or 0.25)
                                        AnimDelay = tick() + swingSpeed
                                        pcall(function()
                                            bedwars.SwordController:playSwordEffect(meta, false)
                                            if meta.displayName:find(' Scythe') then
                                                bedwars.ScytheController:playLocalAnimation()
                                            end
                                        end)
                                        if vape.ThreadFix and setthreadidentity then
                                            pcall(setthreadidentity, 8)
                                        end
                                    end
                                end
                                local currentSwingSpeed = SwingTime and SwingTime.Enabled and SwingTimeSlider.Value or (meta.sword and meta.sword.respectAttackSpeedForEffects and meta.sword.attackSpeed or 0.42)
                                if not (SyncHits and SyncHits.Enabled) or (tick() - swingCooldown) >= math.max(currentSwingSpeed, 0.05) then
                                    swingCooldown = tick()
                                end
                            end
                        end
                    end

                    pcall(function()
                        for i, v in Boxes do
                            v.Adornee = attacked[i] and attacked[i].Entity.RootPart or nil
                            if v.Adornee then
                                v.Color3 = Color3.fromHSV(attacked[i].Check.Hue, attacked[i].Check.Sat, attacked[i].Check.Value)
                                v.Transparency = 1 - attacked[i].Check.Opacity
                            end
                        end
                        for i, v in Particles do
                            v.Position = attacked[i] and attacked[i].Entity.RootPart.Position or Vector3.new(9e9, 9e9, 9e9)
                            v.Parent = attacked[i] and gameCamera or nil
                        end
                    end)

                    if Face and Face.Enabled and attacked[1] then
                        local vec = attacked[1].Entity.RootPart.Position * Vector3.new(1, 0, 1)
                        local targetCFrame = CFrame.lookAt(entitylib.character.RootPart.Position, Vector3.new(vec.X, entitylib.character.RootPart.Position.Y + 0.001, vec.Z))
                        local speed = FaceSpeed and FaceSpeed.Value or 15
                        entitylib.character.RootPart.CFrame = entitylib.character.RootPart.CFrame:Lerp(targetCFrame, math.clamp(speed / 100, 0.01, 1))
                    end

                    pcall(function() if RangeCirclePart ~= nil then RangeCirclePart.Parent = gameCamera end end)
                    task.wait(1 / UpdateRate.Value)
                until not Killaura.Enabled
            else
                stopAutoShootLoop()
                table.clear(ProjectileDelay)
                table.clear(attacked)
                store.KillauraTarget = nil
                for _, v in Boxes do v.Adornee = nil end
                for _, v in Particles do v.Parent = nil end
                if inputService.TouchEnabled then
                    pcall(function() lplr.PlayerGui.MobileUI['2'].Visible = true end)
                end
                Attacking = false
                if armC0 then
                    if AnimTween then AnimTween:Destroy() AnimTween = nil end
                    AnimTween = tweenService:Create(gameCamera.Viewmodel.RightHand.RightWrist, TweenInfo.new(AnimationTween and AnimationTween.Enabled and 0.001 or 0.3, Enum.EasingStyle.Exponential), {
                        C0 = armC0
                    })
                    AnimTween:Play()
                end
                if RangeCirclePart ~= nil then RangeCirclePart:Destroy() end
            end
        end,
        Tooltip = 'Attack players around you\nwithout aiming at them.'
    })

    pcall(function()
        local PSI = Killaura:CreateToggle({
            Name = 'Preserve Sword Icon',
            Function = function(callback)
                preserveSwordIcon = callback
            end,
            Default = true
        })
        PSI.Object.Visible = inputService.TouchEnabled
    end)

    Targets = Killaura:CreateTargets({
        Players = true,
        NPCs = true
    })

    TargetPriority = Killaura:CreateDropdown({
        Name = 'Target Priority',
        List = {'Players First', 'NPCs First', 'Distance'},
        Default = 'Players First',
        Tooltip = 'Choose which targets to prioritize'
    })

    local methods = {'Damage', 'Distance'}
    for i in sortmethods do
        if not table.find(methods, i) then
            table.insert(methods, i)
        end
    end
    SwingRange = Killaura:CreateSlider({
        Name = 'Swing range',
        Min = 1,
        Max = 40,
        Default = 22,
        Suffix = function(val) return val == 1 and 'stud' or 'studs' end
    })
    AttackRange = Killaura:CreateSlider({
        Name = 'Attack range',
        Min = 1,
        Max = 22,
        Default = 22,
        Suffix = function(val) return val == 1 and 'stud' or 'studs' end
    })
    RangeCircle = Killaura:CreateToggle({
        Name = "Range Visualiser",
        Function = function(call)
            if call then
                createRangeCircle()
            else
                if RangeCirclePart then
                    RangeCirclePart:Destroy()
                    RangeCirclePart = nil
                end
            end
        end
    })
    AngleSlider = Killaura:CreateSlider({Name = 'Max angle', Min = 1, Max = 360, Default = 360})
    UpdateRate = Killaura:CreateSlider({Name = 'Update rate', Min = 1, Max = 120, Default = 60, Suffix = 'hz'})
    MaxTargets = Killaura:CreateSlider({Name = 'Max targets', Min = 1, Max = 5, Default = 5})
    Sort = Killaura:CreateDropdown({Name = 'Target Mode', List = methods})
    Mouse = Killaura:CreateToggle({
        Name = 'Require mouse down',
        Function = function(callback)
            if callback and LegitAura and LegitAura.Enabled then
                Mouse:Toggle(false)
                LegitAura:Toggle(false)
                notif("Killaura", "yo u cant have require mouse down AND swing only on at da same time turned both off 4 u ", 5)
            end
        end
    })
    Swing = Killaura:CreateToggle({Name = 'No Swing'})
    GUI = Killaura:CreateToggle({Name = 'GUI check'})
    SwingTime = Killaura:CreateToggle({
        Name = 'Custom Swing Time',
        Function = function(callback)
            SwingTimeSlider.Object.Visible = callback
        end
    })
    SwingTimeSlider = Killaura:CreateSlider({
        Name = 'Swing Time',
        Min = 0,
        Max = 1,
        Default = 0.42,
        Decimal = 100,
        Visible = false
    })
    ContinueSwinging = Killaura:CreateToggle({
        Name = 'Continue Swinging',
        Tooltip = 'Swing X times after losing target (based on swing speed)',
        Function = function(callback)
            if ContinueSwingTime then
                ContinueSwingTime.Object.Visible = callback
            end
        end
    })
    ContinueSwingTime = Killaura:CreateSlider({
        Name = 'Swing Duration',
        Min = 0,
        Max = 5,
        Default = 1,
        Decimal = 10,
        Suffix = 's',
        Visible = false
    })
    CustomHitReg = Killaura:CreateToggle({
        Name = 'Custom Hit Reg',
        Tooltip = 'Limit how many hits per second',
        Function = function(callback)
            if CustomHitRegSlider then
                CustomHitRegSlider.Object.Visible = callback
            end
            if callback then
                lastCustomHitTime = 0
            end
        end
    })
    CustomHitRegSlider = Killaura:CreateSlider({
        Name = 'Hits Per Second',
        Min = 1,
        Max = 36,
        Default = 30,
        Tooltip = 'Maximum hits per second',
        Visible = false
    })
    SyncHits = Killaura:CreateToggle({
        Name = 'Sync Hits',
        Tooltip = 'Waits for sword animation before attacking'
    })
    Killaura:CreateToggle({
        Name = 'Show target',
        Function = function(callback)
            BoxSwingColor.Object.Visible = callback
            BoxAttackColor.Object.Visible = callback
            if callback then
                for i = 1, 10 do
                    local box = Instance.new('BoxHandleAdornment')
                    box.Adornee = nil
                    box.AlwaysOnTop = true
                    box.Size = Vector3.new(3, 5, 3)
                    box.CFrame = CFrame.new(0, -0.5, 0)
                    box.ZIndex = 0
                    box.Parent = vape.gui
                    Boxes[i] = box
                end
            else
                for _, v in Boxes do v:Destroy() end
                table.clear(Boxes)
            end
        end
    })
    BoxSwingColor = Killaura:CreateColorSlider({
        Name = 'Target Color',
        Darker = true,
        DefaultHue = 0.6,
        DefaultOpacity = 0.5,
        Visible = false,
        Function = function(hue, sat, val)
            if Killaura.Enabled and RangeCirclePart ~= nil then
                RangeCirclePart.Color = Color3.fromHSV(hue, sat, val)
            end
        end
    })
    BoxAttackColor = Killaura:CreateColorSlider({
        Name = 'Attack Color',
        Darker = true,
        DefaultOpacity = 0.5,
        Visible = false
    })
    Killaura:CreateToggle({
        Name = 'Target particles',
        Function = function(callback)
            ParticleTexture.Object.Visible = callback
            ParticleColor1.Object.Visible = callback
            ParticleColor2.Object.Visible = callback
            ParticleSize.Object.Visible = callback
            if callback then
                for i = 1, 10 do
                    local part = Instance.new('Part')
                    part.Size = Vector3.new(2, 4, 2)
                    part.Anchored = true
                    part.CanCollide = false
                    part.Transparency = 1
                    part.CanQuery = false
                    part.Parent = Killaura.Enabled and gameCamera or nil
                    local particles = Instance.new('ParticleEmitter')
                    particles.Brightness = 1.5
                    particles.Size = NumberSequence.new(ParticleSize.Value)
                    particles.Shape = Enum.ParticleEmitterShape.Sphere
                    particles.Texture = ParticleTexture.Value
                    particles.Transparency = NumberSequence.new(0)
                    particles.Lifetime = NumberRange.new(0.4)
                    particles.Speed = NumberRange.new(16)
                    particles.Rate = 128
                    particles.Drag = 16
                    particles.ShapePartial = 1
                    particles.Color = ColorSequence.new({
                        ColorSequenceKeypoint.new(0, Color3.fromHSV(ParticleColor1.Hue, ParticleColor1.Sat, ParticleColor1.Value)),
                        ColorSequenceKeypoint.new(1, Color3.fromHSV(ParticleColor2.Hue, ParticleColor2.Sat, ParticleColor2.Value))
                    })
                    particles.Parent = part
                    Particles[i] = part
                end
            else
                for _, v in Particles do v:Destroy() end
                table.clear(Particles)
            end
        end
    })
    ParticleTexture = Killaura:CreateTextBox({
        Name = 'Texture',
        Default = 'rbxassetid://14736249347',
        Function = function()
            for _, v in Particles do
                v.ParticleEmitter.Texture = ParticleTexture.Value
            end
        end,
        Darker = true,
        Visible = false
    })
    ParticleColor1 = Killaura:CreateColorSlider({
        Name = 'Color Begin',
        Function = function(hue, sat, val)
            for _, v in Particles do
                v.ParticleEmitter.Color = ColorSequence.new({
                    ColorSequenceKeypoint.new(0, Color3.fromHSV(hue, sat, val)),
                    ColorSequenceKeypoint.new(1, Color3.fromHSV(ParticleColor2.Hue, ParticleColor2.Sat, ParticleColor2.Value))
                })
            end
        end,
        Darker = true,
        Visible = false
    })
    ParticleColor2 = Killaura:CreateColorSlider({
        Name = 'Color End',
        Function = function(hue, sat, val)
            for _, v in Particles do
                v.ParticleEmitter.Color = ColorSequence.new({
                    ColorSequenceKeypoint.new(0, Color3.fromHSV(ParticleColor1.Hue, ParticleColor1.Sat, ParticleColor1.Value)),
                    ColorSequenceKeypoint.new(1, Color3.fromHSV(hue, sat, val))
                })
            end
        end,
        Darker = true,
        Visible = false
    })
    ParticleSize = Killaura:CreateSlider({
        Name = 'Size',
        Min = 0,
        Max = 1,
        Default = 0.2,
        Decimal = 100,
        Function = function(val)
            for _, v in Particles do
                v.ParticleEmitter.Size = NumberSequence.new(val)
            end
        end,
        Darker = true,
        Visible = false
    })
    Face = Killaura:CreateToggle({
        Name = 'Face target',
        Function = function(callback)
            if FaceSpeed then FaceSpeed.Object.Visible = callback end
        end
    })
    FaceSpeed = Killaura:CreateSlider({
        Name = 'Face Speed',
        Min = 1,
        Max = 100,
        Default = 15,
        Decimal = 10,
        Darker = true,
        Visible = false,
        Tooltip = 'How fast to snap towards target (lower = slower/smoother)'
    })
    Animation = Killaura:CreateToggle({
        Name = 'Custom Animation',
        Function = function(callback)
            AnimationMode.Object.Visible = callback
            AnimationTween.Object.Visible = callback
            AnimationSpeed.Object.Visible = callback
            if Killaura.Enabled then
                Killaura:Toggle()
                Killaura:Toggle()
            end
        end
    })
    local animnames = {}
    for i in anims do table.insert(animnames, i) end
    AnimationMode = Killaura:CreateDropdown({
        Name = 'Animation Mode',
        List = animnames,
        Darker = true,
        Visible = false
    })
    AnimationSpeed = Killaura:CreateSlider({
        Name = 'Animation Speed',
        Min = 0,
        Max = 2,
        Default = 1,
        Decimal = 10,
        Darker = true,
        Visible = false
    })
    AnimationTween = Killaura:CreateToggle({Name = 'No Tween', Darker = true, Visible = false})
    Limit = Killaura:CreateToggle({
        Name = 'Limit to items',
        Function = function(callback)
            if inputService.TouchEnabled and Killaura.Enabled then
                pcall(function() lplr.PlayerGui.MobileUI['2'].Visible = callback end)
            end
        end,
        Tooltip = 'Only attacks when the sword is held'
    })
    LegitAura = Killaura:CreateToggle({
        Name = 'Swing only',
        Tooltip = 'Only attacks while swinging manually',
        Function = function(callback)
            if callback and Mouse and Mouse.Enabled then
                LegitAura:Toggle(false)
                Mouse:Toggle(false)
                notif("Killaura", "yo u cant have swing only AND require mouse down on at da same time lol turned both off 4 u ", 5)
            end
        end
    })
    AirHit = Killaura:CreateToggle({
        Name = 'Air Hits',
        Default = true,
        Tooltip = 'Control hit chance when target is airborne',
        Function = function(callback)
            if AirHitsChance then
                AirHitsChance.Object.Visible = callback
            end
        end
    })
    AirHitsChance = Killaura:CreateSlider({
        Name = 'Air Hits Chance',
        Min = 0,
        Max = 100,
        Default = 100,
        Suffix = '%',
        Decimal = 5,
        Darker = true,
        Visible = false
    })

    local _silasThread = task.spawn(function()
        local wasAvailable = true
        while vape.Loaded do
            task.wait(0.05)
            if bedwars.AbilityController then
                local ok, nowAvailable = pcall(bedwars.AbilityController.canUseAbility, bedwars.AbilityController, 'rebellion_shield')
                nowAvailable = ok and nowAvailable
                if wasAvailable and not nowAvailable then
                    store.silasAbilityTime = tick()
                end
                wasAvailable = nowAvailable
            end
        end
    end)
    local _terraThread = task.spawn(function()
        local wasStompAvailable = true
        local wasKickAvailable = true
        while vape.Loaded do
            task.wait(0.05)
            if bedwars.AbilityController then
                local ok1, nowStomp = pcall(bedwars.AbilityController.canUseAbility, bedwars.AbilityController, 'BLOCK_STOMP')
                local ok2, nowKick = pcall(bedwars.AbilityController.canUseAbility, bedwars.AbilityController, 'BLOCK_KICK')
                nowStomp = ok1 and nowStomp
                nowKick = ok2 and nowKick
                if wasStompAvailable and not nowStomp then store.terraStompTime = tick() end
                if wasKickAvailable and not nowKick then store.terraKickTime = tick() end
                wasStompAvailable = nowStomp
                wasKickAvailable = nowKick
            end
        end
    end)

    kitChecks = {
        ['Sophia'] = function() return isFrozen(nil, FROZEN_THRESHOLD) end,
        ['Sigrid'] = function() return entitylib.isAlive and lplr.Character and lplr.Character:FindFirstChild('elk') ~= nil end,
    }
	DynamicReach = Killaura:CreateToggle({
        Name = 'Dynamic Reach',
        Default = false,
        Tooltip = 'Optimizes hit data and timing at far ranges'
    })
    AttackCheck = Killaura:CreateToggle({
        Name = 'Attack Check',
        Tooltip = 'Stops Killaura when a kit ability is detected (Sophia, etc) or when asleep',
        Function = function(callback) end,
        Default = false
    })

    FastHits = Killaura:CreateToggle({
        Name = 'Fast Hits',
        Tooltip = 'Deals more damage quicker using projectiles',
        Default = false,
        Function = function(call)
            FastHitsMode.Object.Visible = call
            FireRate.Object.Visible = call and FastHitsMode.Value == 'NEWFastHits'
            if LegitSwitch then LegitSwitch.Object.Visible = call and FastHitsMode.Value == 'NEWFastHits' end
            if OldShootInterval then OldShootInterval.Object.Visible = call and FastHitsMode.Value == 'OLDFastHits' end
            if OldSwitchDelay then OldSwitchDelay.Object.Visible = call and FastHitsMode.Value == 'OLDFastHits' end
            if OldWaitDelay then OldWaitDelay.Object.Visible = call and FastHitsMode.Value == 'OLDFastHits' end
            if OldFirstPersonCheck then OldFirstPersonCheck.Object.Visible = call and FastHitsMode.Value == 'OLDFastHits' end
            if call then
                 if Killaura and Killaura.Enabled then
                    startAutoShootLoop()
                end
            else
                stopAutoShootLoop()
            end
        end
    })
    FastHitsMode = Killaura:CreateDropdown({
        Name = 'Fast Hits Mode',
        List = {'NEWFastHits', 'OLDFastHits'},
        Default = 'NEWFastHits',
        Darker = true,
        Visible = false,
        Function = function(val)
            FireRate.Object.Visible = val == 'NEWFastHits'
            LegitSwitch.Object.Visible = val == 'NEWFastHits'
            OldShootInterval.Object.Visible = val == 'OLDFastHits'
            OldSwitchDelay.Object.Visible = val == 'OLDFastHits'
            OldWaitDelay.Object.Visible = val == 'OLDFastHits'
            OldFirstPersonCheck.Object.Visible = val == 'OLDFastHits'
        end
    })
    LegitSwitch = Killaura:CreateToggle({
        Name = 'Legit Switch',
        Default = false,
        Darker = true,
        Visible = false,
        Tooltip = 'Uses hotbarSwitch to switch to crossbow before shooting instead of silent switch'
    })
    OldShootInterval = Killaura:CreateSlider({
        Name = 'Shoot Interval',
        Min = 0.1, Max = 3, Default = 0.5, Decimal = 10, Suffix = 's',
        Darker = true, Visible = false,
        Tooltip = 'How often to shoot bows'
    })
    OldSwitchDelay = Killaura:CreateSlider({
        Name = 'Switch Delay',
        Min = 0, Max = 0.2, Default = 0.05, Decimal = 100, Suffix = 's',
        Darker = true, Visible = false,
        Tooltip = 'Delay between switching and shooting'
    })
    OldWaitDelay = Killaura:CreateSlider({
        Name = 'Wait Delay',
        Min = 0, Max = 1, Default = 0, Decimal = 100, Suffix = 's',
        Darker = true, Visible = false,
        Tooltip = 'Delay before shooting'
    })
    OldFirstPersonCheck = Killaura:CreateToggle({
        Name = 'First Person Only',
        Default = false, Darker = true, Visible = false,
        Tooltip = 'Only works in first person mode'
    })
    FireRate = Killaura:CreateSlider({
        Name = 'Fire rate',
        Suffix = 's',
        Min = 0, Max = 2, Decimal = 100,
        Darker = true, Visible = false,
        Default = 0
    })

    task.defer(function()
        if AirHit and AirHit.Enabled and AirHitsChance and AirHitsChance.Object then
            AirHitsChance.Object.Visible = true
        end
    end)
end)
